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
use std::collections::HashMap;
use std::convert::TryInto;
use std::fmt::Debug;
use std::fmt::Display;
use std::rc::Rc;
use std::rc::Weak;

use super::node_hash::AccumulatorHash;
use super::proof::Proof;
use super::stump::Stump;
use super::util::detect_row;
use super::util::detwin;
use super::util::get_proof_positions;
use super::util::is_root_populated;
use super::util::is_root_position;
use super::util::left_child;
use super::util::max_position_at_row;
use super::util::parent;
use super::util::right_child;
use super::util::root_position;
use super::util::tree_rows;

#[derive(Default, Clone)]
/// A node in the Pollard tree
struct PollardNode<Hash: AccumulatorHash> {
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
    hash: Cell<Hash>,
    /// This node's aunt
    ///
    /// The aunt is the sibling of the parent. This is the only node that is not owned by this
    /// node, as it is owned by some ancestor. This is a [Weak] reference to avoid cycles in the tree.
    /// If a node is a root, this value is `None`, as it doesn't have an aunt. If this node's
    /// parent is a root, then it actually points to its parent, as the parent is a root, and
    /// there's no aunt.
    aunt: RefCell<Option<Weak<Self>>>,
    /// This node's left niece
    ///
    /// The left niece is the left child of this node's sibling. We use an actual [Rc] here, to
    /// make this node own the niece. This is the only place where an [Rc] can be stored past some
    /// function's scope, as it may create cycles in the tree. This is a [RefCell] because we may
    /// need to either prune the nieces, or swap them if this node is a root. If this node is a
    /// leaf, this value is `None`, as it doesn't have any descendants.
    left_niece: RefCell<Option<Rc<Self>>>,
    /// This node's right niece
    ///
    /// The right niece is the right child of this node's sibling. We use an actual [Rc] here, to
    /// make this node own the niece. This is the only place where an [Rc] can be stored past some
    /// function's scope, as it may create cycles in the tree. This is a [RefCell] because we may
    /// need to either prune the nieces, or swap them if this node is a root. If this node is a
    /// leaf, this value is `None`, as it doesn't have any descendants.
    right_niece: RefCell<Option<Rc<Self>>>,
}

pub enum PollardError<Hash: AccumulatorHash> {
    /// We couldn't find the requested node inside map
    ///
    /// This is either due to this node not existing at all, or due to it being pruned. If the node
    /// was pruned, we can't generate a proof for it, as we don't have the necessary data.
    NodeNotFound(Hash),

    /// We couldn't find the requested position inside the forest
    ///
    /// We've tried to fetch a position that doesn't exist inside this forest, or we don't have the
    /// branch for. You can know whether it should exist by looking at the number of leaves in the
    /// forest, and the position you're trying to fetch.
    PositionNotFound(u64),

    /// The proof is invalid
    ///
    /// We've tried to ingest a proof that is invalid. This may be due to the proof being tampered
    /// with, or due to the UTXO actually not being in the accumulator. When designing protocols
    /// or implementing Bitcoin-related Utreexo stuff, make sure you account for proofs being
    /// malleated by some untrusted third-party, so and invalid proofs doesn't necessarily mean
    /// that the UTXO is not in the accumulator.
    InvalidProof,

    /// We've had some I/O error while serializing or deserializing the forest
    IO(std::io::Error),

    /// We couldn't upgrade a node to a root
    ///
    /// This should never happen, as it would mean that a child was pruned before its parent, which
    /// is a bug in the code. If you see this error, please report it to the developers.
    CouldNotUpgradeNode,

    /// We couldn't find the children of a node
    ///
    /// This could happen in a variety of situations, but it's generally a bug in the code. If you
    /// see this error, please report it to the developers.
    CouldNotFindChildren,

    /// We couldn't find the aunt of a node
    ///
    /// This could happen in a variety of situations, but it's generally a bug in the code. If you
    /// see this error, please report it to the developers.
    AuntNotFound,

    /// We couldn't find the sibling of a node
    ///
    /// This could happen in a variety of situations, but it's generally a bug in the code. If you
    /// see this error, please report it to the developers.
    SiblingNotFound,

    /// We couldn't find the niece of a node
    ///
    /// This could happen in a variety of situations, but it's generally a bug in the code. If you
    /// see this error, please report it to the developers.
    NieceNotFound,

    /// Couldn't find the root for a given subtree
    ///
    /// Probably due to an invalid proof passed during deletion
    RootNotFound,
}

impl<Hash: AccumulatorHash> From<std::io::Error> for PollardError<Hash> {
    fn from(err: std::io::Error) -> Self {
        Self::IO(err)
    }
}

impl<Hash: AccumulatorHash> PartialEq for PollardError<Hash> {
    #[allow(unused)] // false positive
    fn eq(&self, other: &Self) -> bool {
        matches!(self, other)
    }
}

impl<Hash: AccumulatorHash> Debug for PollardError<Hash> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NodeNotFound(hash) => write!(f, "Node not found: {hash}"),
            Self::PositionNotFound(pos) => write!(f, "Position not found: {pos}"),
            Self::InvalidProof => write!(f, "Invalid proof"),
            Self::IO(err) => write!(f, "IO error: {err}"),
            Self::CouldNotUpgradeNode => {
                write!(f, "Could not upgrade node, this is probably a bug")
            }
            Self::CouldNotFindChildren => {
                write!(f, "BUG: Could not find children in a case where it should")
            }
            Self::AuntNotFound => write!(f, "Could not find the aunt of a node in a case where it probably should, this might be a bug"),
            Self::SiblingNotFound => write!(f, "Could not find the sibling of a node in a case where it probably should, this might be a bug"),
            Self::NieceNotFound => write!(f, "Could not find the niece of a node in a case where it probably should, this might be a bug"),
            Self::RootNotFound => write!(f, "Could not find the root for a given subtree. Your proof is probably invalid"),
        }
    }
}

impl<Hash: AccumulatorHash> std::fmt::Display for PollardError<Hash> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}

impl<Hash: AccumulatorHash> Debug for PollardNode<Hash> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.hash().to_string())
    }
}

impl<Hash: AccumulatorHash> PartialEq for PollardNode<Hash> {
    fn eq(&self, other: &Self) -> bool {
        self.hash() == other.hash()
    }
}

// we mostly use it for testing
impl<Hash: AccumulatorHash> Eq for PollardNode<Hash> {}

impl<Hash: AccumulatorHash> PollardNode<Hash> {
    /// Creates a new PollardNode with the given hash and remember value
    fn new(hash: Hash, remember: bool) -> Rc<Self> {
        Rc::new(Self {
            remember,
            hash: Cell::new(hash),
            aunt: RefCell::new(None),
            left_niece: RefCell::new(None),
            right_niece: RefCell::new(None),
        })
    }

    fn serialize<W: std::io::Write>(&self, writer: &mut W) -> Result<(), PollardError<Hash>> {
        let is_leaf = self.left_niece().is_none() as u8;
        writer.write_all(&is_leaf.to_be_bytes())?;

        let self_hash = self.hash();
        self_hash.write(writer)?;

        if is_leaf == 0 {
            self.left_niece()
                .ok_or(PollardError::CouldNotFindChildren)?
                .serialize(writer)?;

            self.right_niece()
                .ok_or(PollardError::CouldNotFindChildren)?
                .serialize(writer)?;
        }

        Ok(())
    }

    fn deserialize<R: std::io::Read>(
        reader: &mut R,
        ancestor: Option<Weak<Self>>,
        leaf_map: &mut HashMap<Hash, Weak<Self>>,
    ) -> Result<Rc<Self>, PollardError<Hash>> {
        let mut is_leaf = [0u8; 1];
        reader.read_exact(&mut is_leaf)?;

        let is_leaf = is_leaf[0];

        let hash = Hash::read(reader)?;

        if is_leaf == 1 {
            let node = Rc::new(Self {
                remember: true,
                hash: Cell::new(hash),
                aunt: RefCell::new(ancestor),
                left_niece: RefCell::new(None),
                right_niece: RefCell::new(None),
            });

            leaf_map.insert(hash, Rc::downgrade(&node));
            return Ok(node);
        }

        let node = Rc::new(Self {
            remember: true,
            hash: Cell::new(hash),
            aunt: RefCell::new(ancestor),
            left_niece: RefCell::new(None),
            right_niece: RefCell::new(None),
        });

        let node_weak = Rc::downgrade(&node);

        let left = Self::deserialize(reader, Some(node_weak.clone()), leaf_map)?;
        let right = Self::deserialize(reader, Some(node_weak), leaf_map)?;

        node.left_niece.replace(Some(left));
        node.right_niece.replace(Some(right));

        Ok(node)
    }

    fn parent(&self) -> Option<Rc<Self>> {
        let granparent = self.grandparent();
        if granparent.is_none() {
            return self.aunt();
        }

        let granparent = granparent.unwrap();
        if granparent.left_niece().eq(&self.aunt()) {
            granparent.right_niece()
        } else {
            granparent.left_niece()
        }
    }

    /// Returns the hash of this node
    fn hash(&self) -> Hash {
        self.hash.get()
    }

    /// Whether we should remember this node or not
    fn should_remember(&self) -> bool {
        let left = self.left_niece();
        let right = self.right_niece();

        match (left, right) {
            (Some(left), Some(right)) => left.should_remember() || right.should_remember(),
            (Some(left), None) => left.should_remember(),
            (None, Some(right)) => right.should_remember(),
            (None, None) => self.remember,
        }
    }

    fn children(&self) -> Option<ChildrenTuple<Hash>> {
        if self.aunt().is_none() {
            return Some((self.left_niece()?, self.right_niece()?));
        }

        let sibling = self.sibling()?;
        Some((sibling.left_niece()?, sibling.right_niece()?))
    }

    /// Returns this node's sibling
    ///
    /// This function should return an [Rc] containing the sibling of this node. If this node is a
    /// root, it should return `None`, as roots don't have siblings.
    fn sibling(&self) -> Option<Rc<Self>> {
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
    fn aunt(&self) -> Option<Rc<Self>> {
        self.aunt.borrow().as_ref()?.upgrade()
    }

    /// Returns this node's grandparent
    ///
    /// This function should return an [Rc] containing the grandparent of this node (i.e. the
    /// parent of this node's parent). If this node is a root, it should return `None`, as roots
    /// don't have grandparents.
    fn grandparent(&self) -> Option<Rc<Self>> {
        self.aunt()?.aunt()
    }

    /// Recomputes the hashes of this node and all of its ancestors
    ///
    /// This function will walk up the tree and recompute the hashes for each node. We may need
    /// this if we delete a node, and we need to update the hashes of the ancestors.
    fn recompute_hashes(&self) {
        if let Some((left, right)) = self.children() {
            let new_hash = Hash::parent_hash(&left.hash(), &right.hash());
            self.hash.set(new_hash);
        }

        if let Some(aunt) = self.aunt() {
            if let Some(parent) = aunt.sibling() {
                return parent.recompute_hashes();
            }

            aunt.recompute_hashes()
        }
    }

    fn recompute_hashes_down(&self) -> Option<()> {
        let left = self.left_niece()?;
        let right = self.right_niece()?;
        let new_hash = Hash::parent_hash(&left.hash(), &right.hash());
        self.hash.set(new_hash);
        left.recompute_hashes_down()?;
        right.recompute_hashes_down()?;
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
    fn migrate_up(&self) -> Result<(), PollardError<Hash>> {
        let aunt = self.aunt().ok_or(PollardError::AuntNotFound)?;
        let grandparent = aunt.aunt().ok_or(PollardError::AuntNotFound)?;
        let parent = aunt.sibling().ok_or(PollardError::SiblingNotFound)?;

        let left_niece = aunt.left_niece().ok_or(PollardError::NieceNotFound)?;

        let _self = if left_niece.hash() == self.hash() {
            aunt.left_niece().ok_or(PollardError::NieceNotFound)?
        } else {
            aunt.right_niece().ok_or(PollardError::NieceNotFound)?
        };

        let left_niece = grandparent
            .left_niece()
            .ok_or(PollardError::NieceNotFound)?;

        let (left_niece, right_niece) = if left_niece.hash() == aunt.hash() {
            let left_niece = grandparent
                .left_niece()
                .ok_or(PollardError::NieceNotFound)?;
            (left_niece, _self.clone())
        } else {
            let right_niece = grandparent
                .right_niece()
                .ok_or(PollardError::NieceNotFound)?;
            (_self.clone(), right_niece)
        };

        // place myself and my parent's sibling as my grandancestor's nieces
        grandparent.set_niece(Some(left_niece), Some(right_niece));

        // update my own aunt
        self.set_aunt(Rc::downgrade(&grandparent));

        aunt.prune();
        // I'm now my aunt's sibling, so I should have their children.
        // Update my nieces's aunt to be me
        if let Some(x) = parent.left_niece() {
            x.set_aunt(Rc::downgrade(&_self))
        };

        if let Some(x) = parent.right_niece() {
            x.set_aunt(Rc::downgrade(&_self))
        }

        // take my parent's nieces, as they are still needed
        self.swap_nieces(&parent);
        _self.recompute_hashes();
        Ok(())
    }

    /// Sets the nieces of this nodes to the provided values
    fn set_niece(&self, left: Option<Rc<Self>>, right: Option<Rc<Self>>) {
        *self.left_niece.borrow_mut() = left;
        *self.right_niece.borrow_mut() = right;
    }

    /// Sets the aunt of this node to the provided value
    fn set_aunt(&self, aunt: Weak<Self>) {
        *self.aunt.borrow_mut() = Some(aunt);
    }

    fn prune(&self) {
        self.left_niece.replace(None);
        self.right_niece.replace(None);
    }

    /// Swaps the nieces of this node with the nieces of the provided node
    ///
    /// We use this function during addition (or undoing an addition) because roots points to their
    /// children, but when we add another node on top of that root, it now should point to the new
    /// node's children. This function swaps the nieces of this node with the nieces of the provided
    /// node.
    fn swap_nieces(&self, other: &Self) {
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
    fn left_niece(&self) -> Option<Rc<Self>> {
        self.left_niece.borrow().clone()
    }

    /// Returns the right niece of this node
    ///
    /// If this node is a leaf, this function should return `None`, as leaves don't have nieces.
    fn right_niece(&self) -> Option<Rc<Self>> {
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
pub struct PollardAddition<Hash> {
    /// The hash of the node to be added
    pub hash: Hash,
    /// Whether we should remember this node or not
    pub remember: bool,
}

#[derive(Clone)]
pub struct Pollard<Hash: AccumulatorHash> {
    /// The roots of our [Pollard]. They are the top nodes of the tree, and they are the only nodes
    /// that are owned by the [Pollard] itself. All other nodes are owned by their ancestors.
    ///
    /// The roots are stored in an array, where the index is the row of the tree where the root is
    /// located. The first root is at index 0, and so on. The roots are stored in the array in the
    /// stack to make it more efficient to access and move them around. At any given time, a row may
    /// or may not have a root. If a row doesn't have a root, the value at that index is `None`.
    roots: [Option<Rc<PollardNode<Hash>>>; 64],
    /// How many leaves have been added to the tree
    ///
    /// We use this value all the time, since everything about the structure of the tree is
    /// reflected in the number of leaves. This value is how many leaves we ever added, so if we
    /// add 5 leaves and delete 4, this value will still be 5. Moreover, the position of a leaf is
    /// the number of leaves when it was added, so we can always find a leaf by it's position.
    leaves: u64,
    leaf_map: HashMap<Hash, Weak<PollardNode<Hash>>>,
}

impl<Hash: AccumulatorHash> PartialEq for Pollard<Hash> {
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

impl<Hash: AccumulatorHash> Eq for Pollard<Hash> {}

impl<Hash: AccumulatorHash> Debug for Pollard<Hash> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.string())
    }
}

impl<Hash: AccumulatorHash> Display for Pollard<Hash> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.string())
    }
}

impl<Hash: AccumulatorHash> Default for Pollard<Hash> {
    fn default() -> Self {
        Self::new()
    }
}

// public methods

impl<Hash: AccumulatorHash> Pollard<Hash> {
    /// Return how many leaves are in the [Pollard]
    pub fn leaves(&self) -> u64 {
        self.leaves
    }

    /// Ingests a proof into the [Pollard], caching the nodes in the proof
    ///
    /// This function takes a proof and a list of hashes for the nodes in that proof. It will
    /// take all the nodes in the proof and add them to the [Pollard], so we can generate proofs
    /// for them later. This function doesn't check the validity of the proof, so you should do
    /// that before calling this function. If the proof is not valid, this function will return an
    /// error.
    pub fn ingest_proof(
        &mut self,
        proof: Proof<Hash>,
        del_hashes: &[Hash],
        remembers: &[u64],
    ) -> Result<(), PollardError<Hash>> {
        self.do_ingest_proof(proof, del_hashes, remembers, false)
    }

    pub fn verify(
        &self,
        proof: &Proof<Hash>,
        del_hashes: &[Hash],
    ) -> Result<bool, PollardError<Hash>> {
        let roots = self.roots();
        proof
            .verify(del_hashes, &roots, self.leaves)
            .map_err(|_| PollardError::InvalidProof)
    }

    pub fn verify_and_ingest(
        &mut self,
        proof: Proof<Hash>,
        del_hashes: &[Hash],
        remembers: &[u64],
    ) -> Result<(), PollardError<Hash>> {
        let roots = self.roots();
        proof
            .verify(del_hashes, &roots, self.leaves)
            .map_err(|_| PollardError::InvalidProof)
            .map(|valid| {
                if !valid {
                    return Err(PollardError::InvalidProof);
                }

                Ok(())
            })??;

        self.do_ingest_proof(proof, del_hashes, remembers, false)
    }

    pub fn prune(&mut self, positions: &[u64]) -> Result<(), PollardError<Hash>> {
        self.prune_map(positions);

        let positions = detwin(positions.to_vec(), tree_rows(self.leaves));
        for node in positions {
            let (node, _) = self
                .grab_position(node)
                .ok_or(PollardError::PositionNotFound(node))?;

            self.leaf_map.remove(&node.hash());
            node.prune();
        }

        Ok(())
    }

    /// Returns the hash of all roots in the [Pollard]
    ///
    /// The returned array contains all roots, in ascending order. You can see the row that each
    /// root occupies by looking at which bits are set in the number of leaves in the [Pollard].
    pub fn roots(&self) -> Vec<Hash> {
        self.roots
            .iter()
            .filter_map(|x| x.as_ref().map(|x| x.hash()))
            .collect()
    }

    /// Proves the inclusion of the nodes at the given positions
    ///
    /// This function takes a list of positions and returns a list of proofs for each position.
    pub fn batch_proof(&self, targets: &[Hash]) -> Result<Proof<Hash>, PollardError<Hash>> {
        let mut target_positions = Vec::new();
        for target in targets {
            let node = self
                .leaf_map
                .get(target)
                .ok_or(PollardError::NodeNotFound(*target))?;

            let position = self.get_pos(node)?;
            target_positions.push(position);
        }

        let proof_positions =
            get_proof_positions(&target_positions, self.leaves, tree_rows(self.leaves));
        let mut proof_hashes = Vec::new();

        for pos in proof_positions.iter() {
            let hash = self
                .grab_position(*pos)
                .ok_or(PollardError::PositionNotFound(*pos))?
                .0
                .hash();

            proof_hashes.push(hash);
        }

        Ok(Proof::<Hash> {
            hashes: proof_hashes,
            targets: target_positions,
        })
    }

    pub fn prove_single(&self, leaf: Hash) -> Result<Proof<Hash>, PollardError<Hash>> {
        let node = self
            .leaf_map
            .get(&leaf)
            .ok_or(PollardError::NodeNotFound(leaf))?;

        let pos = self.get_pos(node)?;
        let hashes = self.prove_single_inner(pos)?;
        let targets = vec![pos];

        Ok(Proof { hashes, targets })
    }

    /// Applies the changes to the [Pollard] for a new block
    ///
    /// Since the order of the operations is important, the API can't expose adding and deleting
    /// directly. Instead, the user should call this function with the additions and deletions they
    /// want to make. You should pass in the additions as [PollardAddition]s, telling what should
    /// be added to the accumulator, and whether it should be remembered or not.
    /// The deletions should be passed as a list of target positions, telling which nodes should be
    /// deleted from the accumulator. Positions that are not cached will be ignored. You should check
    /// the validity of the proof before calling this function, as it will blindly apply the changes
    /// to the [Pollard] without validating anything.
    pub fn modify(
        &mut self,
        adds: &[PollardAddition<Hash>],
        del_hashes: &[Hash],
        proof: Proof<Hash>,
    ) -> Result<(), PollardError<Hash>> {
        let targets = proof.targets.clone();
        self.ingest_proof(proof, del_hashes, &targets)?;

        let targets = detwin(targets, tree_rows(self.leaves));
        let targets = targets
            .iter()
            .map(|x| {
                self.grab_position(*x)
                    .ok_or(PollardError::PositionNotFound(*x))
            })
            .collect::<Vec<_>>();

        for del in targets {
            self.delete_single(del?.0)?
        }

        let mut add_nodes = Vec::new();
        let mut roots_destroyed = Vec::new();
        for node in adds {
            let (_new_nodes, _roots_destroyed) = self.add_single(*node)?;
            add_nodes.extend(_new_nodes);
            roots_destroyed.extend(_roots_destroyed);
        }

        Ok(())
    }

    /// Creates a new empty [Pollard]
    pub fn new() -> Self {
        let roots: [Option<Rc<PollardNode<Hash>>>; 64] = std::array::from_fn(|_| None);
        Self {
            roots,
            leaves: 0,
            leaf_map: HashMap::new(),
        }
    }

    /// Reconstructs the [Pollard] from a set of roots and number of leaves
    ///
    /// One use for a partial pollard is for mempool and wallet implementations, where you need to
    /// keep track of a subset of the whole tree. Instead of remputing the pollard from genesis for
    /// every flavor of accumulator you have, you can sync-up using the [Stump] and then use its
    /// roots to create a up-to-date pollard.
    pub fn from_roots(roots: Vec<Hash>, leaves: u64) -> Self {
        let mut pollard = Self::new();
        pollard.leaves = leaves;

        let roots = (0..=63)
            .map(|x| {
                if is_root_populated(x, leaves) {
                    return Some(PollardNode::<Hash>::new(*roots.get(x as usize)?, true));
                }
                None
            })
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        Self {
            roots,
            leaves,
            leaf_map: HashMap::new(),
        }
    }

    /// Serializes the [Pollard] into a sync
    ///
    /// This function serializes the [Pollard] into a sync that implements [std::io::Write]. This will be
    /// serialized in a compact binary format, so it can be stored in a file or sent over the
    /// network. This function will return an error if it fails to write to the sync.
    ///
    /// To deserialize the [Pollard] back, you can use the [deserialize] function.
    pub fn serialize<W: std::io::Write>(&self, writer: &mut W) -> Result<(), PollardError<Hash>> {
        writer.write_all(&self.leaves.to_be_bytes())?;

        for root in self.roots.iter() {
            match root {
                Some(root) => {
                    let marker = 1u8;
                    writer.write_all(&marker.to_be_bytes())?;
                    root.serialize(writer)?
                }
                None => {
                    let marker = 0u8;
                    writer.write_all(&marker.to_be_bytes())?;
                }
            }
        }

        Ok(())
    }

    /// Deserializes a [Pollard] from a stream
    ///
    /// This function deserializes a [Pollard] from a stream that implements [std::io::Read]. This stream
    /// should contain a [Pollard] serialized with the [serialize] function.
    pub fn deserialize<R: std::io::Read>(reader: &mut R) -> Result<Self, PollardError<Hash>> {
        let mut leaves = [0u8; 8];
        reader.read_exact(&mut leaves)?;
        let leaves = u64::from_be_bytes(leaves);

        let mut pollard = Self::new();
        pollard.leaves = leaves;

        for root in pollard.roots.iter_mut() {
            let mut marker = [0u8; 1];
            reader.read_exact(&mut marker)?;
            let marker = marker[0];

            if marker == 1 {
                *root = Some(PollardNode::<Hash>::deserialize(
                    reader,
                    None,
                    &mut pollard.leaf_map,
                )?);
            }
        }

        Ok(pollard)
    }
}

// private methods

/// The result from add_single
type AddSingleResult<T> = (Vec<(u64, T)>, Vec<usize>);
type ChildrenTuple<Hash> = (Rc<PollardNode<Hash>>, Rc<PollardNode<Hash>>);

impl<Hash: AccumulatorHash> Pollard<Hash> {
    fn prune_map(&mut self, positions: &[u64]) {
        for pos in positions {
            let node = self.grab_position(*pos).unwrap().0;
            self.leaf_map.remove(&node.hash());
        }
    }

    fn grab_position(&self, pos: u64) -> Option<ChildrenTuple<Hash>> {
        let (root, depth, bits) = Self::detect_offset(pos, self.leaves);
        let mut node = self.roots[root as usize].clone()?;

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

    fn ingest_positions(
        &mut self,
        mut iter: impl Iterator<Item = (u64, Hash)>,
        remembers: &[u64],
    ) -> Result<(), PollardError<Hash>> {
        let forest_rows = tree_rows(self.leaves);
        while let Some((pos1, hash1)) = iter.next() {
            if is_root_position(pos1, self.leaves, forest_rows) {
                let root = detect_row(pos1, forest_rows);
                self.roots[root as usize] = Some(PollardNode::new(hash1, true));
                continue;
            }

            let (pos2, hash2) = iter.next().ok_or(PollardError::InvalidProof)?;
            if pos1 != (pos2 ^ 1) {
                return Err(PollardError::InvalidProof);
            }

            let aunt = parent(pos1, forest_rows);
            let aunt = self
                .grab_position(aunt)
                .ok_or(PollardError::AuntNotFound)?
                .1;

            if aunt.left_niece().is_some() {
                continue;
            }

            let new_node = PollardNode::new(hash1, true);
            let new_sibling = PollardNode::new(hash2, true);

            new_node.set_aunt(Rc::downgrade(&aunt));
            new_sibling.set_aunt(Rc::downgrade(&aunt));

            if remembers.contains(&pos1) || remembers.contains(&pos2) {
                self.leaf_map.insert(hash1, Rc::downgrade(&new_node));
                self.leaf_map.insert(hash2, Rc::downgrade(&new_sibling));
            }

            aunt.set_niece(Some(new_sibling), Some(new_node));
        }

        Ok(())
    }

    fn do_ingest_proof(
        &mut self,
        proof: Proof<Hash>,
        del_hashes: &[Hash],
        remembers: &[u64],
        recompute: bool,
    ) -> Result<(), PollardError<Hash>> {
        let forest_rows = tree_rows(self.leaves);
        let (mut all_nodes, _) = proof
            .calculate_hashes(del_hashes, self.leaves)
            .map_err(|_| PollardError::InvalidProof)?;

        let proof_positions = get_proof_positions(&proof.targets, self.leaves, forest_rows);

        all_nodes.extend(proof_positions.into_iter().zip(proof.hashes.clone()));
        all_nodes.sort();
        let iter = all_nodes.into_iter().rev();
        self.ingest_positions(iter, remembers)?;

        let pruned = proof
            .targets
            .iter()
            .filter(|x| !remembers.contains(x))
            .copied()
            .collect::<Vec<_>>();

        self.prune(&pruned)?;

        if recompute {
            for root in self.roots.iter().filter_map(|x| x.as_ref()) {
                root.recompute_hashes_down();
            }
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

    fn get_hash(&self, pos: u64) -> Result<Hash, PollardError<Hash>> {
        match self.grab_position(pos) {
            Some(node) => Ok(node.0.hash()),
            None => Err(PollardError::PositionNotFound(pos)),
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
                a.push_str(&b.as_ref().map(|b| b.hash()).unwrap_or_default().to_string());
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

    fn prove_single_inner(&self, pos: u64) -> Result<Vec<Hash>, PollardError<Hash>> {
        let (node, sibling) = self
            .grab_position(pos)
            .ok_or(PollardError::PositionNotFound(pos))?;
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

    fn add_single(
        &mut self,
        node: PollardAddition<Hash>,
    ) -> Result<AddSingleResult<Hash>, PollardError<Hash>> {
        let mut row = 0;
        let mut new_node = PollardNode::new(node.hash, node.remember);
        self.leaf_map.insert(node.hash, Rc::downgrade(&new_node));

        let mut add_positions = Vec::new();
        let mut roots_to_destroy = Vec::new();

        while self.leaves >> row & 1 == 1 {
            let old_root = std::mem::take(&mut self.roots[row as usize]).expect("Root not found");
            let pos = root_position(self.leaves(), row, tree_rows(self.leaves()));

            add_positions.push((pos, old_root.hash()));

            if old_root.hash().is_empty() {
                let pos = row as usize;
                self.roots[pos] = None;
                roots_to_destroy.push(pos);
                row += 1;
                continue;
            }

            let new_root_hash = Hash::parent_hash(&old_root.hash.get(), &new_node.hash.get());
            let new_root_rc = Rc::new(PollardNode {
                remember: old_root.should_remember() || new_node.should_remember(),
                hash: Cell::new(new_root_hash),
                aunt: RefCell::new(None),
                left_niece: RefCell::new(None),
                right_niece: RefCell::new(None),
            });

            // swap nieces
            new_node.swap_nieces(&old_root);

            //FIXME: This should be a method in PollardNode
            if let Some(x) = new_node.left_niece() {
                x.set_aunt(Rc::downgrade(&new_node))
            }
            if let Some(x) = new_node.right_niece() {
                x.set_aunt(Rc::downgrade(&new_node))
            }

            if let Some(x) = old_root.left_niece() {
                x.set_aunt(Rc::downgrade(&old_root))
            }
            if let Some(x) = old_root.right_niece() {
                x.set_aunt(Rc::downgrade(&old_root))
            }

            // update aunts for the old nodes
            let new_root_weak = Rc::downgrade(&new_root_rc);
            old_root.set_aunt(new_root_weak.clone());
            new_node.set_aunt(new_root_weak);

            // update nieces for the new root
            let (left_niece, right_niece) =
                if old_root.should_remember() || new_node.should_remember() {
                    (Some(old_root), Some(new_node))
                } else {
                    (None, None)
                };

            new_root_rc.set_niece(left_niece, right_niece);

            // keep doing this until we find a row with an empty spot
            new_node = new_root_rc;
            row += 1;
        }

        self.roots[row as usize] = Some(new_node);
        self.leaves += 1;

        Ok((add_positions, roots_to_destroy))
    }

    fn delete_single(&mut self, node: Rc<PollardNode<Hash>>) -> Result<(), PollardError<Hash>> {
        self.leaf_map.remove(&node.hash());
        // we are deleting a root, just write an empty hash where it was
        if node.aunt.borrow().is_none() {
            for i in 0..64 {
                if self.roots[i].eq(&Some(node.clone())) {
                    self.roots[i] = Some(Rc::new(PollardNode::default()));
                    return Ok(());
                }
            }

            return Err(PollardError::RootNotFound);
        }

        let sibling = node.sibling().ok_or(PollardError::SiblingNotFound)?;

        if node.grandparent().is_none() {
            // my parent is a root, I'm a root now
            for i in 0..64 {
                let aunt = node.aunt().ok_or(PollardError::AuntNotFound)?;

                let root = if let Some(root) = self.roots[i].as_ref() {
                    root
                } else {
                    continue;
                };

                if root.hash() == aunt.hash() {
                    self.roots[i] = Some(sibling);
                    return Ok(());
                }
            }

            return Err(PollardError::RootNotFound);
        };

        sibling.migrate_up().unwrap();
        Ok(())
    }

    /// Returns the position in the tree of this node
    fn get_pos(&self, node: &Weak<PollardNode<Hash>>) -> Result<u64, PollardError<Hash>> {
        // This indicates whether the node is a left or right child at each level
        // When we go down the tree, we can use the indicator to know which
        // child to take.
        let mut left_child_indicator = 0_u64;
        let mut rows_to_top = 0;
        let mut node = node.upgrade().ok_or(PollardError::CouldNotUpgradeNode)?;

        while let Some(aunt) = node.parent() {
            let aunt_left = aunt.children().ok_or(PollardError::CouldNotFindChildren)?.0;
            // If the current node is a left child, we left-shift the indicator
            // and leave the LSB as 0
            if aunt_left.hash() == node.hash() {
                left_child_indicator <<= 1;
            } else {
                // If the current node is a right child, we left-shift the indicator
                // and set the LSB to 1
                left_child_indicator <<= 1;
                left_child_indicator |= 1;
            }
            rows_to_top += 1;
            node = aunt;
        }

        let root_row = self.roots.iter().position(|root| {
            if let Some(root) = root {
                return root.hash() == node.hash();
            }

            false
        });

        let forest_rows = tree_rows(self.leaves);
        let root_row = root_row.ok_or(PollardError::RootNotFound)?;

        let mut pos = root_position(self.leaves, root_row as u8, forest_rows);
        for _ in 0..rows_to_top {
            // If LSB is 0, go left, otherwise go right
            match left_child_indicator & 1 {
                0 => {
                    pos = left_child(pos, forest_rows);
                }
                1 => {
                    pos = right_child(pos, forest_rows);
                }
                _ => unreachable!(),
            }
            left_child_indicator >>= 1;
        }

        Ok(pos)
    }
}

impl<Hash: AccumulatorHash> From<Stump<Hash>> for Pollard<Hash> {
    fn from(stump: Stump<Hash>) -> Self {
        Self::from_roots(stump.roots, stump.leaves)
    }
}

#[cfg(test)]
mod tests {
    use std::str::FromStr;

    use serde::Deserialize;

    use super::*;
    use crate::accumulator::node_hash::BitcoinNodeHash;
    use crate::accumulator::util::hash_from_u8;

    #[test]
    fn test_ser_rtt() {
        let mut p = Pollard::<BitcoinNodeHash>::new();
        let adds = vec![
            PollardAddition {
                hash: hash_from_u8(0),
                remember: true,
            },
            PollardAddition {
                hash: hash_from_u8(1),
                remember: true,
            },
            PollardAddition {
                hash: hash_from_u8(2),
                remember: true,
            },
            PollardAddition {
                hash: hash_from_u8(3),
                remember: true,
            },
            PollardAddition {
                hash: hash_from_u8(4),
                remember: true,
            },
            PollardAddition {
                hash: hash_from_u8(5),
                remember: true,
            },
            PollardAddition {
                hash: hash_from_u8(6),
                remember: true,
            },
            PollardAddition {
                hash: hash_from_u8(7),
                remember: true,
            },
            PollardAddition {
                hash: hash_from_u8(8),
                remember: true,
            },
            PollardAddition {
                hash: hash_from_u8(9),
                remember: true,
            },
            PollardAddition {
                hash: hash_from_u8(10),
                remember: true,
            },
            PollardAddition {
                hash: hash_from_u8(11),
                remember: true,
            },
            PollardAddition {
                hash: hash_from_u8(12),
                remember: true,
            },
            PollardAddition {
                hash: hash_from_u8(13),
                remember: true,
            },
            PollardAddition {
                hash: hash_from_u8(14),
                remember: true,
            },
        ];

        let proof = Proof::default();
        let dels = Vec::new();

        p.modify(&adds, &dels, proof.clone()).unwrap();
        p.prune(&[0, 1, 6, 7, 10]).unwrap();

        let mut buffer = Vec::new();
        p.serialize(&mut buffer).unwrap();

        let p2 = Pollard::deserialize(&mut buffer.as_slice()).unwrap();
        assert_eq!(p, p2);
    }

    #[test]
    fn test_from_roots() {
        let roots = vec![
            hash_from_u8(0),
            hash_from_u8(1),
            hash_from_u8(2),
            hash_from_u8(3),
        ];

        let leaves = 15;

        let p = Pollard::<BitcoinNodeHash>::from_roots(roots.clone(), leaves);
        assert_eq!(roots, p.roots());
        assert_eq!(leaves, p.leaves());
    }

    #[test]
    fn test_from_stump() {
        let roots = vec![
            hash_from_u8(0),
            hash_from_u8(1),
            hash_from_u8(2),
            hash_from_u8(3),
        ];
        let leaves = 15;

        let stump = Stump { roots, leaves };
        let p: Pollard<BitcoinNodeHash> = stump.clone().into();

        assert_eq!(stump.roots, p.roots());
        assert_eq!(leaves, p.leaves());
    }

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

        let mut acc = Pollard::<BitcoinNodeHash>::new();
        acc.modify(&hashes, &[], Proof::default()).unwrap();

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

    #[derive(Debug, Deserialize)]
    struct TestCase {
        leaf_preimages: Vec<u8>,
        target_values: Option<Vec<u64>>,
        expected_roots: Vec<String>,
        proofhashes: Option<Vec<String>>,
    }

    #[test]
    fn run_tests_from_cases() {
        #[derive(Deserialize)]
        struct TestsJSON {
            insertion_tests: Vec<TestCase>,
            deletion_tests: Vec<TestCase>,
        }

        let contents = std::fs::read_to_string("test_values/test_cases.json")
            .expect("Something went wrong reading the file");

        let tests = serde_json::from_str::<TestsJSON>(contents.as_str())
            .expect("JSON deserialization error");

        for i in tests.insertion_tests {
            run_single_addition_case(i);
        }

        for i in tests.deletion_tests {
            run_case_with_deletion(i);
        }
    }

    fn run_single_addition_case(case: TestCase) {
        let hashes = case
            .leaf_preimages
            .iter()
            .map(|preimage| {
                let hash = hash_from_u8(*preimage);
                PollardAddition {
                    hash,
                    remember: true,
                }
            })
            .collect::<Vec<_>>();

        let mut p = Pollard::<BitcoinNodeHash>::new();
        p.modify(&hashes, &[], Proof::default()).unwrap();

        let expected_roots = case
            .expected_roots
            .iter()
            .map(|root| BitcoinNodeHash::from_str(root).unwrap())
            .collect::<Vec<_>>();
        let roots = p.roots().iter().copied().rev().collect::<Vec<_>>();

        assert_eq!(roots.len(), case.expected_roots.len());
        assert_eq!(expected_roots, roots, "Test case failed {case:?}");
    }

    fn run_case_with_deletion(case: TestCase) {
        let hashes = case
            .leaf_preimages
            .iter()
            .map(|preimage| {
                let hash = hash_from_u8(*preimage);
                PollardAddition {
                    hash,
                    remember: false,
                }
            })
            .collect::<Vec<_>>();

        let target_hashes = case
            .target_values
            .as_ref()
            .unwrap()
            .iter()
            .map(|target| hash_from_u8(*target as u8))
            .collect::<Vec<_>>();

        let proof_hashes = case
            .proofhashes
            .clone()
            .unwrap_or_default()
            .into_iter()
            .map(|hash| {
                BitcoinNodeHash::from_str(hash.as_str()).expect("Test case hashes are valid")
            })
            .collect::<Vec<_>>();

        let proof = Proof::new(case.target_values.clone().unwrap(), proof_hashes);

        let mut p = Pollard::<BitcoinNodeHash>::new();
        p.modify(&hashes, &[], Proof::default()).unwrap();
        p.modify(&[], &target_hashes, proof).unwrap();

        let expected_roots = case
            .expected_roots
            .iter()
            .map(|root| BitcoinNodeHash::from_str(root).unwrap())
            .collect::<Vec<_>>();

        let roots = p.roots().iter().copied().rev().collect::<Vec<_>>();
        assert_eq!(roots.len(), case.expected_roots.len());
        assert_eq!(expected_roots, roots, "Test case failed {case:?}");
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

        let mut p = Pollard::<BitcoinNodeHash>::new();
        p.modify(&hashes, &[], Proof::default()).unwrap();
        p.delete_single(p.grab_position(1).unwrap().0)
            .expect("Failed to delete");

        let root = p.roots[1].clone();
        assert_eq!(root.unwrap().hash(), hashes[0].hash);
    }

    #[test]
    fn test_ingest_proof_and_prove() {
        // this test will create a forest, prove a few leaves, prune all leaves, ingest the proof
        // and prove the same leaves + siblings again
        let values = vec![0, 1, 2, 3, 4, 5, 6, 7];
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

        let mut acc = Pollard::<BitcoinNodeHash>::new();
        acc.modify(&hashes, &[], Proof::default()).unwrap();

        let del_hashes = [
            hash_from_u8(2),
            hash_from_u8(1),
            hash_from_u8(4),
            hash_from_u8(6),
        ];
        let proof = acc.batch_proof(&del_hashes).unwrap();

        acc.prune(&[0, 1, 2, 3, 4, 5, 6, 7]).unwrap();
        acc.ingest_proof(proof, &del_hashes, &[2, 1, 4, 6]).unwrap();

        let del_hashes = [0, 1, 4, 5, 6, 7]
            .iter()
            .map(|x| hash_from_u8(*x))
            .collect::<Vec<_>>();
        let proof = acc.batch_proof(&del_hashes).unwrap();
        assert!(acc.verify(&proof, &del_hashes).unwrap());
    }
    #[test]
    fn test_prove() {
        let values = vec![0, 1, 2, 3, 4, 5, 6, 7];
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

        let mut acc = Pollard::<BitcoinNodeHash>::new();
        acc.modify(&hashes, &[], Proof::default()).unwrap();
        let del_hashes = [
            hash_from_u8(2),
            hash_from_u8(1),
            hash_from_u8(4),
            hash_from_u8(6),
        ];
        let proof = acc.batch_proof(&del_hashes).unwrap();
        let expected_proof = Proof::new(
            [2, 1, 4, 6].to_vec(),
            vec![
                "6e340b9cffb37a989ca544e6bb780a2c78901d3fb33738768511a30617afa01d"
                    .parse()
                    .unwrap(),
                "084fed08b978af4d7d196a7446a86b58009e636b611db16211b65a9aadff29c5"
                    .parse()
                    .unwrap(),
                "e77b9a9ae9e30b0dbdb6f510a264ef9de781501d7b6b92ae89eb059c5ab743db"
                    .parse()
                    .unwrap(),
                "ca358758f6d27e6cf45272937977a748fd88391db679ceda7dc7bf1f005ee879"
                    .parse()
                    .unwrap(),
            ],
        );

        assert_eq!(proof, expected_proof);
        assert!(acc.verify(&proof, &del_hashes).unwrap());
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

        let mut acc = Pollard::<BitcoinNodeHash>::new();
        acc.modify(&hashes, &[], Proof::default()).unwrap();

        let proof = acc.prove_single(hashes[3].hash).unwrap();
        let expected_hashes = [
            "dbc1b4c900ffe48d575b5da5c638040125f65db0fe3e24494b76ea986457d986",
            "02242b37d8e851f1e86f46790298c7097df06893d6226b7c1453c213e91717de",
        ]
        .iter()
        .map(|x| BitcoinNodeHash::from_str(x).unwrap())
        .collect::<Vec<_>>();

        let expected_proof = Proof {
            hashes: expected_hashes,
            targets: vec![3],
        };

        assert_eq!(proof, expected_proof);
    }

    fn get_hashes_of(values: &[u8]) -> Vec<PollardAddition<BitcoinNodeHash>> {
        values
            .iter()
            .map(|preimage| {
                let hash = hash_from_u8(*preimage);
                PollardAddition {
                    hash,
                    remember: true,
                }
            })
            .collect()
    }

    #[test]
    fn test_get_pos() {
        macro_rules! test_get_pos {
            ($p:ident, $pos:literal) => {
                let node = $p.grab_position($pos).unwrap().0;
                assert_eq!(
                    $p.get_pos(&Rc::downgrade(&node)),
                    Ok($pos),
                    "Failed to get position of node {:?}",
                    node
                );
            };
        }

        let hashes = get_hashes_of(&[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]);
        let mut p = Pollard::new();
        p.modify(&hashes, &[], Proof::default())
            .expect("Test mem_forests are valid");
        test_get_pos!(p, 0);
        test_get_pos!(p, 1);
        test_get_pos!(p, 2);
        test_get_pos!(p, 3);
        test_get_pos!(p, 4);
        test_get_pos!(p, 5);
        test_get_pos!(p, 6);
        test_get_pos!(p, 7);
        test_get_pos!(p, 8);
        test_get_pos!(p, 9);
        test_get_pos!(p, 10);
        test_get_pos!(p, 11);
        test_get_pos!(p, 12);

        let root = p.roots[3].as_ref().unwrap();
        let left = root.left_niece().unwrap();
        let right = root.right_niece().unwrap();

        assert_eq!(p.get_pos(&Rc::downgrade(root)), Ok(28));
        assert_eq!(p.get_pos(&Rc::downgrade(&left)), Ok(24));
        assert_eq!(p.get_pos(&Rc::downgrade(&right)), Ok(25));
    }

    #[test]
    fn test_ingest_proof() {
        let values = [0, 1, 2, 3, 4, 5, 6, 7]
            .iter()
            .map(|pos| {
                let hash = hash_from_u8(*pos);
                PollardAddition {
                    hash,
                    remember: false,
                }
            })
            .collect::<Vec<_>>();

        let proof = Proof {
            targets: [3].to_vec(),
            hashes: [
                "dbc1b4c900ffe48d575b5da5c638040125f65db0fe3e24494b76ea986457d986",
                "02242b37d8e851f1e86f46790298c7097df06893d6226b7c1453c213e91717de",
                "29590a14c1b09384b94a2c0e94bf821ca75b62eacebc47893397ca88e3bbcbd7",
            ]
            .iter()
            .map(|x| BitcoinNodeHash::from_str(x).unwrap())
            .collect::<Vec<_>>(),
        };

        let mut acc = Pollard::<BitcoinNodeHash>::new();
        acc.modify(&values, &[], Proof::default()).unwrap();
        acc.ingest_proof(proof.clone(), &[hash_from_u8(3)], &[3])
            .unwrap();

        let new_proof = acc.prove_single(values[3].hash).unwrap();
        assert_eq!(new_proof, proof);

        let node = acc.grab_position(3).unwrap().0;
        assert_eq!(node.hash(), hash_from_u8(3));
    }
}
