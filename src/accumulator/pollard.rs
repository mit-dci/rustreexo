/// Pollard is an efficient implementation of the accumulator for keeping track of a subset of the
/// whole tree. Instead of storing a proof for some leaves, it is more efficient to hold them in a
/// tree structure, and add/remove elements as needed. The main use-case for a Pollard is to keep
/// track of unconfirmed transactions' proof, in the mempool. As you get new transactions through
/// the p2p network, you check the proofs and add them to the Pollard. When a block is mined, we
/// can remove the confirmed transactions from the Pollard, and keep the unconfirmed ones. We can
/// also serve proofs for specific transactions as requested, allowing efficient transaction relay.
///
/// This implementation is close to the one in `MemForest`, but it is specialized in keeping track
/// of subsets of the whole tree, allowing you to cache and uncache elements as needed. While the
/// MemForest keeps everything in the accumulator, and may take a lot of memory.
///
/// Nodes are kept in memory, and they hold their hashes, a reference to their **aunt** (not
/// parent!), and their nieces (not children!). We do this to allow for proof generation, while
/// prunning as much as possible. In a merkle proof, we only need the sibling of the path to the
/// root, the parent is always computed on the fly as we walk up the tree. Some there's no need to
/// keep the parent. But we need the aunt (the sibling of the parent) to generate the proof.
///
/// Every node is owned by exactly one other node, the ancestor - With the only exception being the
/// roots, which are owned by the Pollard itself. This almost garantees that we can't have a memory
/// leak, as deleting one node will delete all of its descendants. The only way to have a memory
/// leak is if we have a cycle in the tree, which we avoid by only allowing Weak references everywhere,
/// except for the owner of the node. Things are kept in a [Rc] to allow for multiple references to
/// the same node, as we may need to operate on it, and also to allow the nieces to have a reference
/// to their aunt. It could be done with pointers, but it would be more complex and error-prone. The
/// [Rc]s live inside a [RefCell], to allow for interior mutability, as we may need to change the
/// values inside a node. Make sure to avoid leaking a reference to the inner [RefCell] to the outside
/// world, as it may cause race conditions and panics. Every time we use a reference to the inner
/// [RefCell], we make sure to drop it as soon as possible, and that we are the only ones operating
/// on it at that time. For this reason, a [Pollard] is not [Sync], and you'll need to use a [Mutex]
/// or something similar to share it between threads. But it is [Send], as it is safe to send it to
/// another thread - everything is owned by the Pollard and lives on the heap.
///
/// ## Usage
///
/// //TODO: Add usage examples
use std::cell::Cell;
use std::cell::RefCell;
use std::fmt::Debug;
use std::fmt::Display;
use std::mem::MaybeUninit;
use std::rc::Rc;
use std::rc::Weak;

use super::node_hash::NodeHash;
use super::proof::Proof;
use super::util::detect_row;
use super::util::detwin;
use super::util::get_proof_positions;
use super::util::max_position_at_row;
use super::util::parent;
use super::util::root_position;
use super::util::tree_rows;

#[derive(Clone)]
pub struct Pollard {
    /// The roots of our [Pollard]. They are the top nodes of the tree, and they are the only nodes
    /// that are owned by the [Pollard] itself. All other nodes are owned by their ancestors.
    ///
    /// The roots are stored in an array, where the index is the row of the tree where the root is
    /// located. The first root is at index 0, and so on. The roots are stored in the array in the
    /// stack to make it more efficent to access and move them around. At any given time, a row may
    /// or may not have a root. If a row doesn't have a root, the value at that index is `None`.
    pub roots: [Option<Rc<PollardNode>>; 64],
    /// How many leaves have been added to the tree
    ///
    /// We use this value all the time, since everything about the structure of the tree is
    /// reflected in the number of leaves. This value is how many leaves we ever added, so if we
    /// add 5 leaves and delete 4, this value will still be 5. Moreover, the position of a leaf is
    /// the number of leaves when it was added, so we can always find a leaf by it's position.
    pub leaves: u64,
}

impl PartialEq for Pollard {
    fn eq(&self, other: &Self) -> bool {
        self.roots
            .iter()
            .zip(other.roots.iter())
            .all(|(a, b)| match (a, b) {
                (Some(a), Some(b)) => a.hash() == b.hash(),
                (None, None) => true,
                _ => false,
            })
    }
}

impl Eq for Pollard {}

impl Debug for Pollard {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.string())
    }
}

impl Display for Pollard {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.string())
    }
}

impl Default for Pollard {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Default, Clone)]
/// A node in the Pollard tree
pub struct PollardNode {
    /// Whether we should remember this node or not
    ///
    /// If this is set, we keep this node in memory, as well as all of its ancestors needed to
    /// generate a proof for it. If this is not set, we can delete this node and all of its
    /// descendants, as we don't need them anymore. For internal nodes, remember is based on
    /// whether any of the nieces have remember set. For leaves, the user sets this value.
    remember: bool,
    /// The hash of this node
    ///
    /// This is the hash used in the merkle proof. For leaves, this is the hash of the value
    /// committed to. For internal nodes, this is the hash of the concatenation of the hashes of
    /// the children. This value is stored in a [Cell] to allow for interior mutability, as we may
    /// need to change it if some descendant is deleted.
    hash: Cell<NodeHash>,
    /// This node's aunt
    ///
    /// The aunt is the sibling of the parent. This is the only node that is not owned by this
    /// node, as it is owned by some ancestor. This is a [Weak] reference to avoid cycles in the tree.
    /// If a node is a root, this value is `None`, as it doesn't have an aunt. If this node's
    /// parent is a root, then it actually points to its parent, as the parent is a root, and
    /// there's no aunt.
    aunt: RefCell<Option<Weak<PollardNode>>>,
    /// This node's left niece
    ///
    /// The left niece is the left child of this node's sibling. We use an actual [Rc] here, to
    /// make this node own the niece. This is the only place where an [Rc] can be stored past some
    /// function's scope, as it may create cycles in the tree. This is a [RefCell] because we may
    /// need to either prune the nieces, or swap them if this node is a root. If this node is a
    /// leaf, this value is `None`, as it doesn't have any descendants.
    left_niece: RefCell<Option<Rc<PollardNode>>>,
    /// This node's right niece
    ///
    /// The right niece is the right child of this node's sibling. We use an actual [Rc] here, to
    /// make this node own the niece. This is the only place where an [Rc] can be stored past some
    /// function's scope, as it may create cycles in the tree. This is a [RefCell] because we may
    /// need to either prune the nieces, or swap them if this node is a root. If this node is a
    /// leaf, this value is `None`, as it doesn't have any descendants.
    right_niece: RefCell<Option<Rc<PollardNode>>>,
}

impl Debug for PollardNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.hash().to_string())
    }
}

impl PartialEq for PollardNode {
    fn eq(&self, other: &Self) -> bool {
        self.hash() == other.hash()
    }
}

impl Eq for PollardNode {}

impl PollardNode {
    /// Creates a new PollardNode with the given hash and remember value
    pub fn new(hash: NodeHash, remember: bool) -> Rc<PollardNode> {
        Rc::new(PollardNode {
            remember,
            hash: Cell::new(hash),
            aunt: RefCell::new(None),
            left_niece: RefCell::new(None),
            right_niece: RefCell::new(None),
        })
    }

    /// Returns the hash of this node
    pub fn hash(&self) -> NodeHash {
        self.hash.get()
    }

    /// Returns this node's sibling
    ///
    /// This function should return an [Rc] containing the sibling of this node. If this node is a
    /// root, it should return `None`, as roots don't have siblings.
    pub fn sibling(&self) -> Option<Rc<PollardNode>> {
        let aunt = self.aunt()?;
        if aunt.left_niece()?.hash() == self.hash() {
            aunt.right_niece()
        } else {
            aunt.left_niece()
        }
    }

    /// Returns this node's aunt
    ///
    /// This function should return an [Rc] containing the aunt of this node. If this node is a
    /// root, it should return `None`, as roots don't have aunts.
    pub fn aunt(&self) -> Option<Rc<PollardNode>> {
        self.aunt.borrow().as_ref()?.upgrade()
    }

    /// Returns this node's grandparent
    ///
    /// This function should return an [Rc] containing the grandparent of this node (i.e. the
    /// parent of this node's parent). If this node is a root, it should return `None`, as roots
    /// don't have grandparents.
    pub fn grandparent(&self) -> Option<Rc<PollardNode>> {
        self.aunt()?.aunt()
    }

    /// Recomputes the hashes of this node and all of its ancestors
    ///
    /// This function will walk up the tree and recompute the hashes for each node. We may need
    /// this if we delete a node, and we need to update the hashes of the ancestors.
    fn recompute_hashes(&self) -> Option<()> {
        let left = self.left_niece();
        let right = self.right_niece();
        let new_hash = NodeHash::parent_hash(&left?.hash(), &right?.hash());
        self.hash.set(new_hash);

        if let Some(aunt) = self.aunt() {
            aunt.recompute_hashes()?;
        }

        Some(())
    }

    /// Migrates this node up the tree
    ///
    /// The deletion algorithm for utreexo works like this: let's say we have the following tree:
    ///
    /// ```!
    /// 06                                                 
    /// |---------\             
    /// 04        05                   
    /// |-----\   |-----\
    /// 00    01  02   03      
    /// ```
    ///
    /// to delete `03`, we simply move `02` up to `09`'s position, so now we have:
    /// ```!
    /// 06
    /// |---------\
    /// 04        02
    /// |-----\   |-----\
    /// 00    01    --    --
    /// ```
    ///
    /// This function does exactly that. It moves this node up the tree, and updates the hashes
    /// of the ancestors to reflect the new subtree (in the example above, the hash of `06` would
    /// be updated to the hash of 04 and 02).
    pub fn migrate_up(&self) -> Option<()> {
        let aunt = self.aunt().unwrap();
        let grandparent = aunt.aunt()?;
        let sibling = self.sibling().unwrap();
        let _self = if aunt.left_niece()?.hash() == self.hash() {
            aunt.left_niece()
        } else {
            aunt.right_niece()
        };

        let (left_niece, right_niece) = if grandparent.left_niece()?.hash() == aunt.hash() {
            (_self.clone(), grandparent.right_niece())
        } else {
            (grandparent.left_niece(), _self.clone())
        };

        grandparent.set_niece(left_niece, right_niece);

        self.set_niece(Some(aunt), Some(sibling));
        _self?.recompute_hashes()?;
        Some(())
    }

    /// Sets the nieces of this nodes to the provided values
    pub fn set_niece(&self, left: Option<Rc<PollardNode>>, right: Option<Rc<PollardNode>>) {
        *self.left_niece.borrow_mut() = left;
        *self.right_niece.borrow_mut() = right;
    }

    /// Sets the aunt of this node to the provided value
    pub fn set_aunt(&self, aunt: Weak<PollardNode>) {
        *self.aunt.borrow_mut() = Some(aunt);
    }

    /// Swaps the nieces of this node with the nieces of the provided node
    ///
    /// We use this function during addition (or undoing an addition) because roots points to their
    /// children, but when we add another node on top of that root, it now should point to the new
    /// node's children. This function swaps the nieces of this node with the nieces of the provided
    /// node.
    pub fn swap_nieces(&self, other: &PollardNode) {
        std::mem::swap(
            &mut *self.left_niece.borrow_mut(),
            &mut *other.left_niece.borrow_mut(),
        );
        std::mem::swap(
            &mut *self.right_niece.borrow_mut(),
            &mut *other.right_niece.borrow_mut(),
        );
    }

    /// Returns the left niece of this node
    ///
    /// If this node is a leaf, this function should return `None`, as leaves don't have nieces.
    pub fn left_niece(&self) -> Option<Rc<PollardNode>> {
        self.left_niece.borrow().clone()
    }

    /// Returns the right niece of this node
    ///
    /// If this node is a leaf, this function should return `None`, as leaves don't have nieces.
    pub fn right_niece(&self) -> Option<Rc<PollardNode>> {
        self.right_niece.borrow().clone()
    }
}

#[derive(Clone, Copy)]
/// A new node to be added to the [Pollard]
///
/// This node contains the data that should be added to the accumulator. It contains the hash of
/// the node, and whether we should remember this node or not. If remember is set, we keep this
/// node in our forest and we can generate proofs for it. If remember is not set, we can delete
/// this node and all of its descendants, as we don't need them anymore.
pub struct PollardAddition {
    /// The hash of the node to be added
    pub hash: NodeHash,
    /// Whether we should remember this node or not
    pub remember: bool,
}

/// Data required to undo a modification to the accumulator.
///
/// If a block gets reorged, we need to undo the changes made to the accumulator we did for it.
/// This struct holds all the data needed to undo the changes made to the [Pollard] for a given
/// block, and the user should keep this data around until it is convinced that the block is
/// not going to be reorged out (or forever, if you want to keep the undo data around).
pub struct UndoData {
    /// Data needed to undo an addition to the [Pollard]. See [UndoDataAddition] for more info.
    add: UndoDataAddition,
}

/// This is returner every time we add new nodes to the [Pollard], and contains every information
/// needed to undo the addition. This is useful in case of reorgs, where we need to undo the
/// changes made in the last few blocks.
struct UndoDataAddition {
    /// How many leaves we've added to the [Pollard]
    num_adds: u64,
    /// The positions of empty roots we've destroyed while adding the leaves
    roots_destroyed: Vec<u8>,
}

// public methods

impl Pollard {
    /// Proves the inclusion of the nodes at the given positions
    ///
    /// This function takes a list of positions and returns a list of proofs for each position.
    pub fn prove(&self, positions: &[u64]) -> Result<Vec<Vec<NodeHash>>, &'static str> {
        // FIXME: return a Proof
        detwin(positions.to_vec(), tree_rows(self.leaves))
            .iter()
            .map(|pos| self.prove_single(*pos))
            .collect()
    }

    /// Undoes the changes made to the [Pollard] for the given [UndoData]
    pub fn undo(&mut self, undo_data: UndoData) {
        for _ in 0..undo_data.add.num_adds {
            self.undo_single_add();
        }

        for i in undo_data.add.roots_destroyed {
            let leaves = self.leaves - undo_data.add.num_adds;
            let pos = root_position(leaves, i, tree_rows(leaves));
            self.roots[i as usize] = Some(PollardNode::new(NodeHash::empty(), false));
        }

        self.leaves -= undo_data.add.num_adds;
    }

    /// Applies the changes to the [Pollard] for a new block
    pub fn modify(&mut self, adds: &[PollardAddition], del_positions: &[u64]) {
        detwin(del_positions.to_vec(), tree_rows(self.leaves))
            .into_iter()
            .map(|pos| self.grab_position(pos))
            .collect::<Vec<_>>()
            .iter()
            .for_each(|del| {
                if let Some(node) = del {
                    self.delete_single(node.clone().0).unwrap();
                }
            });

        for node in adds {
            self.add_single(*node);
        }
    }

    /// Creates a new empty [Pollard]
    pub fn new() -> Self {
        const EMPTY_ROOT: Option<Rc<PollardNode>> = None;
        let roots: [Option<Rc<PollardNode>>; 64] = [EMPTY_ROOT; 64];
        Self { roots, leaves: 0 }
    }
}

// private methods

impl Pollard {
    fn grab_position(&self, pos: u64) -> Option<(Rc<PollardNode>, Rc<PollardNode>)> {
        let (root, depth, bits) = Self::detect_offset(pos, self.leaves);
        let mut node = self.roots[root as usize].as_ref().unwrap().clone();

        if depth == 0 {
            return Some((node.clone(), node));
        }

        for row in 0..(depth - 1) {
            let next = if pos >> (depth - row - 1) & 1 == 1 {
                node.left_niece()?
            } else {
                node.right_niece()?
            };
            node = next;
        }

        Some(if bits & 1 == 0 {
            (node.left_niece()?, node.right_niece()?)
        } else {
            (node.right_niece()?, node.left_niece()?)
        })
    }

    fn ingest_proof(&self, proof: Proof, del_hashes: &[NodeHash]) -> Result<(), String> {
        let (mut nodes, _) = proof.calculate_hashes(del_hashes, self.leaves)?;
        let proof_positions =
            get_proof_positions(&proof.targets, self.leaves, tree_rows(self.leaves));
        nodes.extend(proof_positions.into_iter().zip(proof.hashes));
        let forest_rows = tree_rows(self.leaves);
        for nodes in nodes.chunks(2).rev() {
            let (pos1, hash1) = nodes[0];
            let (pos2, hash2) = nodes[1];

            let parent = parent(pos1, forest_rows);
            let parent = self.grab_position(parent).ok_or("Parent not found")?.0;
            let new_node = PollardNode::new(hash1, true);
            let new_sibling = PollardNode::new(hash2, true);

            parent.set_niece(Some(new_sibling), Some(new_node));
        }

        Ok(())
    }

    fn detect_offset(pos: u64, num_leaves: u64) -> (u8, u8, u64) {
        let mut tr = tree_rows(num_leaves);
        let nr = detect_row(pos, tr);

        let mut bigger_trees = tr;
        let mut marker = pos;

        while ((marker << nr) & ((2 << tr) - 1)) >= ((1 << tr) & num_leaves) {
            let tree_size = (1 << tr) & num_leaves;
            marker -= tree_size;
            bigger_trees -= 1;

            tr -= 1;
        }
        (bigger_trees, (tr - nr), marker)
    }

    fn get_hash(&self, pos: u64) -> Result<NodeHash, &'static str> {
        match self.grab_position(pos) {
            Some(node) => Ok(node.0.hash()),
            None => Err("Position not found"),
        }
    }

    /// to_string returns the full mem_forest in a string for all forests less than 6 rows.
    fn string(&self) -> String {
        if self.leaves == 0 {
            return "empty".to_owned();
        }
        let fh = tree_rows(self.leaves);
        // The accumulator should be less than 6 rows.
        if fh > 6 {
            let s = format!("Can't print {} leaves. roots: \n", self.leaves);
            return self.roots.iter().fold(s, |mut a, b| {
                a.extend(
                    b.as_ref()
                        .map(|b| b.hash())
                        .unwrap_or(NodeHash::empty())
                        .to_string()
                        .chars(),
                );
                a
            });
        }

        let mut output = vec!["".to_string(); (fh as usize * 2) + 1];
        let mut pos: u8 = 0;
        for h in 0..=fh {
            let row_len = 1 << (fh - h);
            for _ in 0..row_len {
                let max = max_position_at_row(h, fh, self.leaves).unwrap();
                if max >= pos as u64 {
                    match self.get_hash(pos as u64) {
                        Ok(val) => {
                            if pos >= 100 {
                                output[h as usize * 2].push_str(
                                    format!("{:#02x}:{} ", pos, &val.to_string()[..2]).as_str(),
                                );
                            } else {
                                output[h as usize * 2].push_str(
                                    format!("{:0>2}:{} ", pos, &val.to_string()[..4]).as_str(),
                                );
                            }
                        }
                        Err(_) => {
                            output[h as usize * 2].push_str("        ");
                        }
                    }
                }

                if h > 0 {
                    output[(h as usize * 2) - 1].push_str("|-------");

                    for _ in 0..((1 << h) - 1) / 2 {
                        output[(h as usize * 2) - 1].push_str("--------");
                    }
                    output[(h as usize * 2) - 1].push_str("\\       ");

                    for _ in 0..((1 << h) - 1) / 2 {
                        output[(h as usize * 2) - 1].push_str("        ");
                    }

                    for _ in 0..(1 << h) - 1 {
                        output[h as usize * 2].push_str("        ");
                    }
                }
                pos += 1;
            }
        }

        output.iter().rev().fold(String::new(), |mut a, b| {
            a.push_str(b);
            a.push('\n');
            a
        })
    }

    fn prove_single(&self, pos: u64) -> Result<Vec<NodeHash>, &'static str> {
        let (node, sibling) = self.grab_position(pos).ok_or("Position not found")?;
        let mut proof = vec![sibling.hash()];
        let mut current = node;

        while let Some(aunt) = current.aunt() {
            // don't push roots
            if aunt.aunt().is_some() {
                proof.push(aunt.hash());
            }
            current = aunt;
        }

        Ok(proof)
    }

    fn undo_single_add(&mut self) {
        let first_row = self.roots.iter().position(|x| x.is_some()).unwrap();

        if first_row == 0 {
            self.roots[0] = None;
            return;
        }

        let node = self.roots[first_row].as_ref().unwrap().clone();
        let old_root = node.left_niece.borrow().as_ref().unwrap().clone();
        let undo_node = node.right_niece.borrow().as_ref().unwrap().clone();

        // unswap nieces
        std::mem::swap(
            &mut undo_node.left_niece.borrow_mut(),
            &mut old_root.left_niece.borrow_mut(),
        );

        std::mem::swap(
            &mut undo_node.right_niece.borrow_mut(),
            &mut old_root.right_niece.borrow_mut(),
        );

        // update aunts for the old root
        *old_root.aunt.borrow_mut() = None;
        self.roots[first_row - 1] = Some(old_root);
        self.roots[first_row] = None;
        self.leaves -= 1;
        drop(node);
    }

    fn add_single(&mut self, node: PollardAddition) {
        let mut row = 0;
        let mut new_node = PollardNode::new(node.hash, node.remember);
        while self.leaves >> row & 1 == 1 {
            let old_root =
                std::mem::replace(&mut self.roots[row as usize], None).expect("Root not found");

            if old_root.hash().is_empty() {
                self.roots[row as usize] = None;
                row += 1;
                continue;
            }

            let new_root_hash = NodeHash::parent_hash(&old_root.hash.get(), &new_node.hash.get());
            let remember = old_root.remember || new_node.remember;
            let new_root_rc = Rc::new(PollardNode {
                remember,
                hash: Cell::new(new_root_hash),
                aunt: RefCell::new(None),
                left_niece: RefCell::new(None),
                right_niece: RefCell::new(None),
            });

            // swap nieces
            new_node.swap_nieces(&old_root);

            //FIXME: This should be a method in PollardNode
            new_node
                .left_niece()
                .map(|x| x.set_aunt(Rc::downgrade(&new_node)));
            new_node
                .right_niece()
                .map(|x| x.set_aunt(Rc::downgrade(&new_node)));

            old_root
                .left_niece()
                .map(|x| x.set_aunt(Rc::downgrade(&old_root)));
            old_root
                .right_niece()
                .map(|x| x.set_aunt(Rc::downgrade(&old_root)));

            if remember {
                // update aunts for the old nodes
                let new_root_weak = Rc::downgrade(&new_root_rc);
                old_root.set_aunt(new_root_weak.clone());
                new_node.set_aunt(new_root_weak);

                // update nieces for the new root
                new_root_rc.set_niece(Some(old_root), Some(new_node));
            }

            // keep doing this until we find a row with an empty spot
            new_node = new_root_rc;
            row += 1;
        }

        self.roots[row as usize] = Some(new_node);
        self.leaves += 1;
    }

    fn delete_single(&mut self, node: Rc<PollardNode>) -> Result<(), &'static str> {
        // we are deleting a root, just write an empty hash where it was
        if node.aunt.borrow().is_none() {
            for i in 0..64 {
                if self.roots[i].as_ref().unwrap().hash() == node.hash() {
                    self.roots[i] = Some(Rc::new(PollardNode::default()));
                    return Ok(());
                }
            }

            return Err("Root not found");
        }

        let sibling = node.sibling().ok_or("Sibling not found")?;
        if node.grandparent().is_none() {
            // my parent is a root, I'm a root now
            for i in 0..64 {
                let aunt = node.aunt().unwrap();
                let Some(root) = self.roots[i].as_ref() else {
                    continue;
                };
                if root.hash() == aunt.hash() {
                    self.roots[i] = Some(sibling);
                    return Ok(());
                }
            }

            return Err("Root not found");
        };

        sibling.migrate_up();
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use std::str::FromStr;

    use super::*;
    use crate::accumulator::util::hash_from_u8;

    #[test]
    fn test_add() {
        let values = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14];
        let hashes = values
            .into_iter()
            .map(|preimage| {
                let hash = hash_from_u8(preimage);
                PollardAddition {
                    hash,
                    remember: true,
                }
            })
            .collect::<Vec<_>>();

        let mut acc = Pollard::new();
        acc.modify(&hashes, &[]);

        assert_eq!(
            "b151a956139bb821d4effa34ea95c17560e0135d1e4661fc23cedc3af49dac42",
            acc.roots[3].as_ref().unwrap().hash().to_string(),
        );
        assert_eq!(
            "9c053db406c1a077112189469a3aca0573d3481bef09fa3d2eda3304d7d44be8",
            acc.roots[2].as_ref().unwrap().hash().to_string(),
        );
        assert_eq!(
            "55d0a0ef8f5c25a9da266b36c0c5f4b31008ece82df2512c8966bddcc27a66a0",
            acc.roots[1].as_ref().unwrap().hash().to_string()
        );
        assert_eq!(
            "4d7b3ef7300acf70c892d8327db8272f54434adbc61a4e130a563cb59a0d0f47",
            acc.roots[0].as_ref().unwrap().hash().to_string()
        );
    }

    #[test]
    fn test_migrate_up() {
        // This tests our code using for deletion. We manually create something like:
        //
        //         grandparent
        //       /             \
        //    aunt         parent
        //  /      \      /      \
        // sibling  self
        //
        // and then we delete self, which should migrate up the sibling to the aunt's position
        // creating:
        //
        //          grandparent
        //        /            \
        //      sibling        parent
        //      /   \          /   \
        let grandparent = PollardNode::new(hash_from_u8(0),true);
        let aunt = PollardNode::new(hash_from_u8(1), true);
        let parent = PollardNode::new(hash_from_u8(2), true);

        grandparent.set_niece(Some(aunt.clone()), Some(parent.clone()));

        parent.set_aunt(Rc::downgrade(&aunt));
        aunt.set_aunt(Rc::downgrade(&grandparent));

        let sibling = PollardNode::new(hash_from_u8(3), true);
        let _self = PollardNode::new(hash_from_u8(4), true);

        aunt.set_niece(Some(sibling.clone()), Some(_self.clone()));
        sibling.set_aunt(Rc::downgrade(&aunt));
        _self.set_aunt(Rc::downgrade(&aunt));

        _self.migrate_up();

        assert_eq!(grandparent.left_niece(), Some(_self));
        assert_eq!(grandparent.right_niece(), Some(parent));
    }

    #[test]
    fn test_undo_single_add() {
        let values1 = vec![0, 1, 2, 3, 4, 5];
        let hashes1 = values1
            .into_iter()
            .map(|preimage| {
                let hash = hash_from_u8(preimage);
                PollardAddition {
                    hash,
                    remember: true,
                }
            })
            .collect::<Vec<_>>();

        let mut acc1 = Pollard::new();
        acc1.modify(&hashes1, &[]);
        acc1.undo_single_add();

        let values2 = vec![0, 1, 2, 3, 4];
        let hashes2 = values2
            .into_iter()
            .map(|preimage| {
                let hash = hash_from_u8(preimage);
                PollardAddition {
                    hash,
                    remember: true,
                }
            })
            .collect::<Vec<_>>();

        let mut acc2 = Pollard::new();
        acc2.modify(&hashes2, &[]);

        assert_eq!(acc1, acc2);
    }

    #[test]
    fn test_delete_roots_child() {
        // Assuming the following tree:
        //
        // 02
        // |---\
        // 00  01
        // If I delete `01`, then `00` will become a root, moving it's hash to `02`
        let values = vec![0, 1];
        let hashes: Vec<_> = values
            .into_iter()
            .map(|preimage| {
                let hash = hash_from_u8(preimage);
                PollardAddition {
                    hash,
                    remember: true,
                }
            })
            .collect();

        let mut p = Pollard::new();
        p.modify(&hashes, &[]);
        p.delete_single(p.grab_position(1).unwrap().0)
            .expect("Failed to delete");

        let root = p.roots[1].clone();
        assert_eq!(root.unwrap().hash(), hashes[0].hash);
    }

    #[test]
    fn test_prove_single() {
        let values = vec![0, 1, 2, 3, 4, 5];
        let hashes: Vec<_> = values
            .into_iter()
            .map(|preimage| {
                let hash = hash_from_u8(preimage);
                let remember = true;
                PollardAddition { hash, remember }
            })
            .collect();

        let mut acc = Pollard::new();
        acc.modify(&hashes, &[]);

        let proof = acc.prove_single(3).unwrap();
        let expected = [
            "dbc1b4c900ffe48d575b5da5c638040125f65db0fe3e24494b76ea986457d986",
            "02242b37d8e851f1e86f46790298c7097df06893d6226b7c1453c213e91717de",
        ]
        .iter()
        .map(|x| NodeHash::from_str(x).unwrap())
        .collect::<Vec<_>>();

        assert_eq!(proof, expected);
    }

    #[test]
    fn test() {
        let values = vec![0, 1, 2, 3, 4, 5];
        let hashes: Vec<_> = values
            .into_iter()
            .map(|preimage| {
                let hash = hash_from_u8(preimage);
                PollardAddition {
                    hash,
                    remember: true,
                }
            })
            .collect();

        let mut acc = Pollard::new();
        acc.modify(&hashes, &[]);
        println!("{}", acc);

        let node = acc.grab_position(8).unwrap();
        println!("{:?}", node.0.hash());
        println!("{:?}", node.0.left_niece());
        println!("{:?}", node.0.right_niece());
    }
}
