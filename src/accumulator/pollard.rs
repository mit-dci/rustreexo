//! This is the Rust implementation of the Pollard data structure, the algorithms are similar
//! to the go counterpart, but it's not a 1-to-1 re-implementation. A tight copy of the Go lib
//! is almost impossible in safe Rust, because it relies on passing pointers around.
//!
//! In a Pollard, nodes points to its niece instead of children. This helps with proving and
//! some updates, but creates some challenges when dealing with Rust. Furthermore, nodes also
//! points to its aunt, creating a link that is hard to express in safe Rust using basic
//! static borrow check and lifetime annotation.
//! # Usage
//! ```
//! use rustreexo::accumulator::pollard::Pollard;
//! use bitcoin_hashes::{sha256::Hash as Data, Hash, HashEngine, hex::ToHex};
//! // Instead of hashing UTXOs, we hash integers for the sake of the example. But in a real
//! // case, you'll take the sha512_256 of LeafData
//! let values = vec![0, 1, 2, 3, 4, 5, 6, 7];
//! // Hashes all values, using just sha256
//! let hashes: Vec<_> = values.into_iter().map(|val|{
//!     let mut engine = Data::engine();
//!     engine.input(&[val]);
//!     Data::from_engine(engine)
//! })
//! .collect();
//! // Creates a new Pollard with 8 leaves, then deletes the first and fourth elements (0, 3)
//! let p = Pollard::new()
//!     .modify(hashes.clone(), vec![])
//!     .expect("Simple addition don't fail")
//!     .modify(vec![], vec![0, 3])
//!     .expect("Nor should simple deletion with known to be in tree elements");
//! // We should get this state after
//! assert_eq!(p.get_roots().len(), 1);
//! assert_eq!(p.get_roots()[0].get_data().to_hex(), String::from("dd015199c18dcd8b8606a4f0053a2ad4797e82f51944d9d2d3cc0c1fca872a22"));
//! ```
//! # Implementation
//! During development of this struct, something much simpler like this code bellow have been tried,
//! but 'ancestor usually binds to the same lifetime as the whole tree, making it impossible to
//! hold a node and a `mut ref` to another one, or the tree itself (usually a vector of roots). We
//! need to mutate internally, and we need to mutate internal node data, like data, aunt and nieces
//! because nodes change their position as the tree get things added and deleted. If you try to
//! introduce more specifiers, you end up with a infinite recursion where you have to specify
//! all lifetimes to descendant and ancestor nodes; impossible to do.
//! ```
//! use bitcoin_hashes::sha256::Hash;
//! use std::boxed::Box;
//! struct PolNode<'ancestor> {
//!     data: Hash,
//!     aunt: &'ancestor PolNode<'ancestor>,
//!     l_niece: Box<PolNode<'ancestor>>,
//!     r_niece: Box<PolNode<'ancestor>>,
//! }
//! ```
//! Note: This [Box] is required because at declaration time, [PolNode] is an incomplete type
//! with no known compilation-time size (i.e !sized), hence, we can't use it as a concrete type.
//! Boxes are complete types, so we place a Box inside [PolNode] and somehow get a new [PolNode]
//! to put in there.
//!
//! The solution is to use [RefCell], a pointer-ish struct that holds a memory location with
//! dynamic borrow checking. Everything the borrow checker do on compilation time, [RefCell] do
//! at runtime. A bit of performance loss, but not that bad. With [RefCell] we can deal with
//! immutable references almost everywhere, and simplify things a lot. We also put a [PolNode] inside
//! a [Rc], so we can keep references to it easily, and even manipulate nodes by their own
//! without risking creating two different trees - If we just clone a node (node a [Rc] of a node)
//! we'll also clone all nodes bellow, creating two identical trees. Every change to this new
//! tree wouldn't reflect on the original one.
//!
//! Even though [RefCell] is considered safe code, it might panic in situations that the
//! borrow checker issues a compile-time error. For that reason, we should be careful when
//! using it. ** It is prohibited to get a mut ref (&mut) to a node inside any tree **, this
//! makes sure we don't run on a conflict of trying mutable borrow a node that is already
//! borrowed. We also avoid immutable refs (&), to the same reason. For all cases of interior
//! mutability, there is a simple specialized function to do the job, and the API gives you
//! a [Rc] over a node, not the [RefCell], so avoid using the [RefCell] directly.

use super::{
    types::{self, parent_hash},
    util::{self, is_left_niece, is_root_position, tree_rows},
};
use bitcoin_hashes::{
    hex::ToHex,
    sha256::{self, Hash},
};
use std::{cell::Cell, fmt::Debug};
use std::{cell::RefCell, rc::Rc};

/// Type alias used throughout this lib, see the crate-level doc to understand why using [Rc]
type Node = Rc<PolNode>;

/// A PolNode is any node inside a tree, it can be a root, in which case aunt would be [None].
/// A internal node, where all fields are filled, or a leaf, that has no child/niece.
/// Mutable references are discouraged, for mutating a [PolNode], use the appropriated
/// methods.
#[derive(Clone, PartialEq, Eq, Default)]
pub struct PolNode {
    data: Cell<Hash>,
    aunt: RefCell<Option<Node>>,
    l_niece: RefCell<Option<Node>>,
    r_niece: RefCell<Option<Node>>,
}

//FIX-ME: Make this Debug more pleasant, like the Go one
impl Debug for PolNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fn fmt_row(
            f: &mut std::fmt::Formatter<'_>,
            row_nodes: Vec<Option<Rc<PolNode>>>,
            i: u32,
        ) -> std::fmt::Result {
            if row_nodes.iter().all(|el| el.is_none()) {
                return Ok(());
            }
            let mut next_nodes = vec![];
            for node in row_nodes {
                if let Some(node) = node {
                    write!(f, "{} ", node.get_data()[0..2].to_hex())?;

                    let (l, r) = node.get_children();
                    next_nodes.push(l);
                    next_nodes.push(r);
                } else {
                    next_nodes.push(None);
                    next_nodes.push(None);

                    write!(f, "---- ")?;
                }
            }
            writeln!(f)?;
            fmt_row(f, next_nodes, i + 1)
        }
        fmt_row(f, vec![Some(self.clone().into_rc())], 0)?;
        Ok(())
    }
}

impl PolNode {
    /// Creates a new [PolNode] with provided data. For an empty node see [Default].
    /// If this node is a root, there's no aunt. If it's a leaf, then nieces is [None]. Finally
    /// if node is a root child, [l_niece] and [r_niece] are actually r_child and l_child (and
    /// aunt is actually parent).
    fn new(
        data: Hash,
        aunt: Option<Node>,
        l_niece: Option<Node>,
        r_niece: Option<Node>,
    ) -> PolNode {
        PolNode {
            data: Cell::new(data),
            aunt: RefCell::new(aunt),
            l_niece: RefCell::new(l_niece),
            r_niece: RefCell::new(r_niece),
        }
    }
    /// Returns the node's data, i.e the stored hash
    pub fn get_data(&self) -> Hash {
        self.data.to_owned().into_inner()
    }
    /// Updates this node's aunt
    fn _update_aunt(&self, aunt: Option<Node>, root: bool) {
        let aunt = if root {
            self.set_aunt(None);
            aunt
        } else if PolNode::_is_l_niece(&aunt.clone().unwrap(), &self.clone().into_rc()) {
            aunt.expect("msg").get_l_niece()
        } else {
            aunt.expect("msg").get_r_niece()
        };
        if let Some(l_niece) = self.get_l_niece() {
            l_niece._update_aunt(aunt.clone(), false);
        }
        if let Some(r_niece) = self.get_l_niece() {
            r_niece._update_aunt(aunt, false);
        }
    }
    /// Returns whether or not `n` is `aunt's` left niece
    fn _is_l_niece(aunt: &Node, n: &Node) -> bool {
        aunt.get_l_niece().as_ref().eq(&Some(n))
    }
    /// Returns whether or not `n` is `aunt's` right niece
    fn get_children(&self) -> (Option<Node>, Option<Node>) {
        let sibling = self.get_sibling();
        if let Some(sibling) = sibling {
            return (sibling.get_l_niece(), sibling.get_r_niece());
        }
        // I'm a root, so I point to my children
        if self.get_aunt().is_none() {
            return (self.get_l_niece(), self.get_r_niece());
        }
        // This means I'm a leaf
        (None, None)
    }
    /// Returns this node's sibling
    fn get_sibling(&self) -> Option<Node> {
        let node = self.get_aunt();
        if let Some(parent) = node {
            if parent.get_l_niece().unwrap_or_default().as_ref().eq(self) {
                return parent.get_r_niece();
            } else {
                return parent.get_l_niece();
            }
        }

        None
    }
    /// Returns this node's parent, this is one of the most important methods, because
    /// most of the data is retrieved from this.
    fn get_parent(&self) -> Option<Node> {
        //I'm a root, so no parent
        self.get_aunt()?;
        if let Some(aunt) = self.get_aunt() {
            // If aunt also has an aunt, then I take his sibling, as he's my parent
            if let Some(grandpa) = aunt.get_aunt() {
                // If my grandparent's left niece is my aunt, then my parent is the right niece
                if grandpa.get_l_niece().eq(&Some(aunt)) {
                    return grandpa.get_r_niece();
                } else {
                    // Here is the opposite
                    return grandpa.get_l_niece();
                }
            } else {
                // If my aunt has no aunt, it means he's a root, and roots points to it's children
                return Some(aunt);
            }
        }

        None
    }
    /// This method is a little evolved, it takes an [Rc] to our aunt, then finds out
    /// whether we are left or right nieces. With that info, we replace the corresponding
    /// aunt's niece with our new self.
    fn set_self_hash(&self, new: Hash) {
        self.data.replace(new);
    }
    /// Transverses the tree upwards, updating the node's hashes after an deletion
    fn recompute_parent_hash(&self) {
        if let (Some(l_niece), Some(r_niece)) = self.get_children() {
            let new_parent_hash = parent_hash(&l_niece.get_data(), &r_niece.get_data());
            let parent = self.get_parent();
            self.set_self_hash(new_parent_hash);

            if let Some(parent) = parent {
                return parent.recompute_parent_hash();
            } else {
                return;
            }
        }
        if let Some(parent) = self.get_parent() {
            return parent.recompute_parent_hash();
        }
        unreachable!();
    }
    /// Returns this node's aunt as [Node]
    fn get_aunt(&self) -> Option<Node> {
        self.aunt.clone().into_inner()
    }
    /// Returns this node's l_niece as [Node]
    fn get_l_niece(&self) -> Option<Node> {
        self.l_niece.borrow().clone()
    }
    /// Returns this node's r_niece as [Node]
    fn get_r_niece(&self) -> Option<Node> {
        self.r_niece.borrow().clone()
    }
    /// Creates a new [PolNode] and returns it as [Node], i.e [Rc<Box<PolNode>>]
    /// If you need a pure PolNode, use `new` instead.
    fn new_node(
        data: Hash,
        aunt: Option<Node>,
        l_niece: Option<Node>,
        r_niece: Option<Node>,
    ) -> Node {
        let node = PolNode {
            data: Cell::new(data),
            aunt: RefCell::new(aunt),
            l_niece: RefCell::new(l_niece),
            r_niece: RefCell::new(r_niece),
        };

        node.into_rc()
    }
    /// Swap this node's aunt with `other`
    fn swap_aunt(&self, other: &Node) {
        self.aunt.swap(&other.aunt);
    }
    /// Returns the current node as an Reference Counted Container "[Rc]". This is how
    /// nodes are stored inside the tree.
    fn into_rc(self) -> Node {
        Rc::new(self)
    }
    /// Set this node's aunt
    fn set_aunt(&self, aunt: Option<Node>) {
        self.aunt.replace(aunt);
    }
    /// Set both r_niece and l_niece
    fn set_nieces(&self, l_niece: Option<Node>, r_niece: Option<Node>) {
        self.l_niece.replace(l_niece);
        self.r_niece.replace(r_niece);
    }
    /// Chops down any subtree this node has
    fn chop(&self) {
        self.l_niece.replace(None);
        self.r_niece.replace(None);
    }
}
/// A Pollard is a collection of trees that may or may not be pruned. We store all roots in
/// the `roots` field. If we choose not to prune, all nodes will be owned by its ancestor
#[derive(Clone, Default)]
pub struct Pollard {
    /// Leaves are the actual data in the accumulator. Each UTXO will be a leaf, this is how
    /// many leafs there are this acc. Note that with swappiless deletion, deleting leaves don't change
    /// this number. So this is more like "How many leaves have we ever added into the acc"
    leaves: u64,
    /// The actual roots
    roots: Vec<Node>,
    /// Whether or not we cache non-roots nodes
    full: bool,
}

impl Pollard {
    /// Creates an empty Pollard
    /// # Example
    /// ```
    /// use rustreexo::accumulator::pollard::Pollard;
    /// let p = Pollard::new();
    /// // Should have no roots
    /// assert_eq!(p.get_roots().len(), 0);
    /// ```
    pub fn new() -> Pollard {
        Pollard {
            leaves: 0,
            roots: vec![],
            full: true,
        }
    }
    /// Modify is the main API to a [Pollard]. Because order matters, you can only `modify`
    /// a [Pollard], and internally it'll add and delete, in the correct order.
    ///
    /// Modify takes ownership over the [Pollard] and returns a new one. This is to avoid API
    /// misuse, since modify is a **pure function**, it doesn't change any of it's arguments
    /// and return a brand new [Pollard]. Taking ownership discourage people to use an old [Pollard]
    /// state instead of using the new one.
    ///
    /// This method accepts two vectors as parameter, a vec of [Hash] and a vec of [u64]. The
    /// first one is a vec of leaf hashes for the newly created UTXOs. The second one is the position
    /// for the UTXOs being spent in this block as inputs.
    ///
    /// # Example
    /// ```
    /// use rustreexo::accumulator::pollard::Pollard;
    /// use bitcoin_hashes::{sha256::Hash as Data, Hash, HashEngine};
    /// let values = vec![0, 1, 2, 3, 4, 5, 6, 7];
    /// let hashes = values.into_iter().map(|val|{
    ///     let mut engine = Data::engine();
    ///     engine.input(&[val]);
    ///     Data::from_engine(engine)
    /// })
    /// .collect();
    /// // Add 8 leaves to the pollard
    /// let p = Pollard::new()
    ///        .modify(hashes, vec![])
    ///        .expect("Pollard should not fail");
    /// assert_eq!(p.get_roots()[0].get_data().to_string(), String::from("b151a956139bb821d4effa34ea95c17560e0135d1e4661fc23cedc3af49dac42"));
    /// ```
    pub fn modify(self, utxos: Vec<Hash>, stxos: Vec<u64>) -> Result<Pollard, String> {
        let utxos_after_deletion = self.leaves + utxos.len() as u64;
        let full = self.full;
        let leaves = self.leaves;
        let roots = self.delete(stxos)?;
        let roots = Pollard::add(roots, utxos, leaves);

        Ok(Pollard {
            leaves: utxos_after_deletion,
            roots,
            full,
        })
    }
    /// Returns a reference to this acc roots. Usually, API consumers won't care much about
    /// roots, serialization should use standard APIs.
    pub fn get_roots(&self) -> &Vec<Node> {
        &self.roots
    }
    /// Deletes a single node from a Pollard. The algorithm works as follows:
    /// Grab a node, it's sibling and it's parent.
    /// (i) if I'm deleting the node, but not it's sibling, then the sibling takes the parent's position
    /// (ii) if both are being deleted, then the parent is also deleted
    /// (iii) if my parent is a root, then the node's sibling becomes a root
    /// (iv) if I'm a root myself, then this root becomes an empty root (PolNode::Default).
    fn delete_single(&mut self, pos: u64) -> Result<(), String> {
        // In what subtree we are?
        let (tree, _, _) = super::util::detect_offset(pos, self.leaves);

        // If deleting a root, we just place a default node in it's place
        if is_root_position(pos, self.leaves, tree_rows(self.leaves)) {
            self.roots[tree as usize] = PolNode::default().into_rc();
            return Ok(());
        }
        // Grab the node we'll move up
        // from_node is whomever is moving up, to node is the position it will be
        // after moved
        let (from_node, _, to_node) = self.grab_node(pos)?;
        // If the position I'm moving to has an aunt, I'm not becoming a root.
        // ancestor is the node right beneath the to_node, this is useful because
        // either it or it's sibling points to the `to_node`. We need to update this.
        if let Some(sibling) = to_node.get_sibling() {
            // If my new ancestor has a sibling, it means my aunt/parent is not root
            // and my aunt is pointing to me, *not* my parent.
            sibling.chop();
            to_node.set_self_hash(from_node.get_data());
            to_node.set_nieces(to_node.get_l_niece(), to_node.get_r_niece());
            to_node.recompute_parent_hash();
        } else {
            // This means we are a root's sibling. We are becoming a root now
            to_node.set_self_hash(from_node.get_data());
            to_node.set_nieces(from_node.get_l_niece(), from_node.get_l_niece());
        }
        Ok(())
    }
    /// Grabs node given its position in the tree. It returns a node's sibling, the node
    /// itself and the parent. Error if node isn't on tree.
    fn grab_node(&self, pos: u64) -> Result<(Node, Node, Node), String> {
        let (tree, branch_len, bits) = super::util::detect_offset(pos, self.leaves);
        let mut n = Some(self.roots[tree as usize].clone());
        let mut sibling = Some(self.roots[tree as usize].clone());
        let mut parent = sibling.clone();

        for row in (0..(branch_len)).rev() {
            // Parent is the sibling of the current node as each of the
            // nodes point to their nieces.
            parent = sibling;

            // Figure out which node we need to follow.
            let niece_pos = ((bits >> row) & 1) as u8;
            if let Some(node) = n {
                if is_left_niece(niece_pos as u64) {
                    n = node.l_niece.clone().into_inner();
                    sibling = node.r_niece.clone().into_inner();
                } else {
                    n = node.r_niece.clone().into_inner();
                    sibling = node.l_niece.clone().into_inner();
                }
            } else {
                sibling = None;
            }
        }
        if let (Some(node), Some(sibling), Some(parent)) = (n, sibling, parent) {
            return Ok((node, sibling, parent));
        }
        Err(format!("node {} not found", pos))
    }
    /// Add nodes to the accumulator
    fn add(mut roots: Vec<Node>, utxos: Vec<Hash>, mut num_leaves: u64) -> Vec<Node> {
        for utxo in utxos {
            roots = Pollard::add_single(roots, utxo, num_leaves);
            num_leaves += 1;
        }

        roots
    }
    /// Deletes nodes from the accumulator
    fn delete(mut self, stxos: Vec<u64>) -> Result<Vec<Node>, String> {
        let stxos = util::detwin(stxos, util::tree_rows(self.leaves));
        for stxo in stxos {
            self.delete_single(stxo)?;
        }

        Ok(self.roots)
    }
    /// Adds a single node. Addition is a loop over all new nodes, calling add_single for each
    /// of them
    fn add_single(mut roots: Vec<Node>, node: Hash, mut num_leaves: u64) -> Vec<Node> {
        let mut node = PolNode::new(node, None, None, None).into_rc();

        while num_leaves & 1 == 1 {
            // If num_leaves & 1 == 1, roots cannot be None
            let left_root = roots
                .pop()
                .expect("add_single: num_leaves & 1 == 1 and no roots?");
            //If the root that we're gonna hash with is empty, move the current
            // node up to the position of the parent.
            //
            // Example:
            //
            // 12
            // |-------\
            // 08      09
            // |---\   |---\
            // 00  01  02  03  --
            //
            // When we add 05 to this tree, 04 is empty so we move 05 to 10.
            // The resulting tree looks like below. The hash at position 10
            // is not hash(04 || 05) but just the hash of 05.
            //
            // 12
            // |-------\
            // 08      09      10
            // |---\   |---\   |---\
            // 00  01  02  03  --  --
            // We accomplish this by just skipping the append-and-hash for 04

            if left_root.get_data() == sha256::Hash::default() {
                continue;
            }
            // Roots points to their children, but now they aren't roots, so they should
            // point to their nieces instead
            left_root.l_niece.swap(&node.l_niece);
            left_root.r_niece.swap(&node.r_niece);
            // Swap aunts for the nieces
            left_root
                .get_l_niece()
                .unwrap_or_default()
                .swap_aunt(&node.get_l_niece().unwrap_or_default());

            left_root
                .get_r_niece()
                .unwrap_or_default()
                .swap_aunt(&node.get_r_niece().unwrap_or_default());
            // Creates a new node that is hash(left_root | node)
            let n_hash = types::parent_hash(&left_root.get_data(), &node.get_data());
            let new_node = PolNode::new_node(n_hash, None, None, None);
            // Turns left_root and node into new_nodes's children
            left_root.set_aunt(Some(new_node.clone()));
            node.set_aunt(Some(new_node.clone()));

            new_node.set_nieces(Some(left_root), Some(node));
            node = new_node;

            num_leaves >>= 1;
        }

        roots.push(node);
        roots
    }
}

#[cfg(test)]
mod test {
    use std::{str::FromStr, vec};

    use super::{PolNode, Pollard};
    use bitcoin_hashes::{
        hex::{FromHex, ToHex},
        sha256::{self, Hash as Data},
        Hash, HashEngine,
    };
    use serde::Deserialize;

    fn hash_from_u8(value: u8) -> Data {
        let mut engine = Data::engine();

        engine.input(&[value]);

        Hash::from_engine(engine)
    }
    #[test]
    fn test_grab_node() {
        let values = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14];
        let hashes = values.into_iter().map(hash_from_u8).collect();

        let p = Pollard::new()
            .modify(hashes, vec![])
            .expect("Pollard should not fail");
        let node = p.grab_node(4).unwrap();
        let target: Data = "e52d9c508c502347344d8c07ad91cbd6068afc75ff6292f062a09ca381c89e71"
            .parse()
            .unwrap();
        let sibling: Data = "e77b9a9ae9e30b0dbdb6f510a264ef9de781501d7b6b92ae89eb059c5ab743db"
            .parse()
            .unwrap();
        let parent: Data = "9eec588c41d87b16b0ee226cb38da3864f9537632321d8be855a73d5616dcc73"
            .parse()
            .unwrap();

        let found_target = node.1.get_data();
        let found_sibling = node.0.get_data();
        let found_parent = node.2.get_data();

        assert_eq!(target, found_target);
        assert_eq!(sibling, found_sibling);
        assert_eq!(parent, found_parent);
    }
    #[test]
    fn test_recompute_hashes() {
        let values = vec![0, 1, 2, 3];
        let hashes = values.into_iter().map(hash_from_u8).collect();

        let p = Pollard::new()
            .modify(hashes, vec![])
            .expect("Pollard should not fail");
        let node = p.grab_node(0);
        if let Ok((node, _, _)) = node {
            node.set_self_hash(
                sha256::Hash::from_hex(
                    "0100000000000000000000000000000000000000000000000000000000000000",
                )
                .unwrap(),
            );
            node.recompute_parent_hash();
            assert_eq!(
                p.get_roots()[0].get_data().to_hex(),
                String::from("a3fab668c6917a4979627f04dd0be687ceb5601aaf161664747ddb1399b1a4fb")
            )
        } else {
            unreachable!()
        }
    }
    #[test]
    fn test_aunt() {
        let values = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14];
        let hashes = values.into_iter().map(hash_from_u8).collect();

        let p = Pollard::new()
            .modify(hashes, vec![])
            .expect("Pollard should not fail");
        let node = p.grab_node(1);

        assert!(node.is_ok());
        let node = node.unwrap();
        let sibling = node.0;
        let self_node = node.1;
        let parent = node.2;

        assert_eq!(
            sibling.get_data().to_string().as_str(),
            "6e340b9cffb37a989ca544e6bb780a2c78901d3fb33738768511a30617afa01d"
        );
        assert_eq!(
            self_node.get_data().to_string().as_str(),
            "4bf5122f344554c53bde2ebb8cd2b7e3d1600ad631c385a5d7cce23c7785459a"
        );
        assert_eq!(
            parent.get_data().to_string().as_str(),
            "02242b37d8e851f1e86f46790298c7097df06893d6226b7c1453c213e91717de"
        );
        assert_eq!(
            self_node
                .get_aunt()
                .unwrap()
                .get_data()
                .to_string()
                .as_str(),
            "9576f4ade6e9bc3a6458b506ce3e4e890df29cb14cb5d3d887672aef55647a2b"
        );
    }
    #[test]
    fn test_delete() {
        let values = vec![0, 1, 2, 3, 4, 5, 6, 7];
        let hashes = values.into_iter().map(hash_from_u8).collect();

        let p = Pollard::new()
            .modify(hashes, vec![])
            .expect("Pollard should not fail");
        let p = p.modify(vec![], vec![0]).expect("msg");

        let (_, node, _) = p.grab_node(8).unwrap();
        assert_eq!(
            String::from("4bf5122f344554c53bde2ebb8cd2b7e3d1600ad631c385a5d7cce23c7785459a"),
            node.get_data().to_string()
        );
    }
    #[test]
    fn test_add() {
        let values = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14];
        let hashes = values.into_iter().map(hash_from_u8).collect();

        let roots = Pollard::add(vec![], hashes, 0);

        assert_eq!(
            "b151a956139bb821d4effa34ea95c17560e0135d1e4661fc23cedc3af49dac42",
            roots[0].get_data().to_string().as_str(),
        );
        assert_eq!(
            "9c053db406c1a077112189469a3aca0573d3481bef09fa3d2eda3304d7d44be8",
            roots[1].get_data().to_string().as_str(),
        );
        assert_eq!(
            "55d0a0ef8f5c25a9da266b36c0c5f4b31008ece82df2512c8966bddcc27a66a0",
            roots[2].get_data().to_string().as_str(),
        );
        assert_eq!(
            "4d7b3ef7300acf70c892d8327db8272f54434adbc61a4e130a563cb59a0d0f47",
            roots[3].get_data().to_string().as_str(),
        );
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
        let hashes: Vec<Data> = values.into_iter().map(hash_from_u8).collect();

        let mut p = Pollard::new()
            .modify(hashes.clone(), vec![])
            .expect("Pollard should not fail");
        p.delete_single(1).expect("msg");
        assert_eq!(p.get_roots().len(), 1);

        let root = p.get_roots()[0].clone();
        assert_eq!(root.get_data(), hashes[0]);
    }
    #[test]
    fn test_get_children() {
        let values = vec![0, 1, 2, 3, 4, 5, 6, 7];
        let hashes: Vec<Data> = values.into_iter().map(hash_from_u8).collect();

        let p = Pollard::new()
            .modify(hashes.clone(), vec![])
            .expect("Pollard should not fail");

        let (sibling, node, _) = p.grab_node(8).expect("Node exists");
        assert_eq!(
            Data::from_str("02242b37d8e851f1e86f46790298c7097df06893d6226b7c1453c213e91717de")
                .unwrap(),
            node.get_data()
        );

        assert_eq!(
            Data::from_str("9576f4ade6e9bc3a6458b506ce3e4e890df29cb14cb5d3d887672aef55647a2b")
                .unwrap(),
            sibling.get_data()
        );
        let (l_child, r_child) = node.get_children();
        assert!(l_child.is_some());
        assert!(r_child.is_some());

        let l_child = l_child.unwrap();
        let r_child = r_child.unwrap();

        assert_eq!(hashes[1], r_child.get_data());
        assert_eq!(hashes[0], l_child.get_data());
    }
    #[test]
    fn test_get_sibling() {
        let values = vec![0, 1, 2, 3, 4, 5, 6, 7];
        let hashes: Vec<Data> = values.into_iter().map(hash_from_u8).collect();

        let p = Pollard::new()
            .modify(hashes, vec![])
            .expect("Pollard should not fail");

        let (sibling, node, _) = p.grab_node(8).expect("Node exists");
        assert_eq!(
            Data::from_str("02242b37d8e851f1e86f46790298c7097df06893d6226b7c1453c213e91717de")
                .unwrap(),
            node.get_data()
        );

        assert_eq!(
            Data::from_str("9576f4ade6e9bc3a6458b506ce3e4e890df29cb14cb5d3d887672aef55647a2b")
                .unwrap(),
            sibling.get_data()
        );
        let sibling = node.get_sibling();
        assert_eq!(
            Data::from_str("9576f4ade6e9bc3a6458b506ce3e4e890df29cb14cb5d3d887672aef55647a2b")
                .unwrap(),
            sibling.unwrap().get_data()
        );
    }
    #[test]
    fn test_get_parent() {
        let values = vec![0, 1, 2, 3, 4, 5, 6, 7];
        let hashes: Vec<Data> = values.into_iter().map(hash_from_u8).collect();

        let p = Pollard::new()
            .modify(hashes, vec![])
            .expect("Pollard should not fail");

        let (_, node, _) = p.grab_node(8).expect("Node exists");
        assert_eq!(
            Data::from_str("02242b37d8e851f1e86f46790298c7097df06893d6226b7c1453c213e91717de")
                .unwrap(),
            node.get_data()
        );
        let parent = node.get_parent();
        assert_eq!(
            parent.unwrap().get_data().to_string(),
            String::from("df46b17be5f66f0750a4b3efa26d4679db170a72d41eb56c3e4ff75a58c65386")
        );
    }
    #[test]
    fn test_delete_root() {
        // Assuming the following tree:
        //
        // 02
        // |---\
        // 00  01
        // If I delete `02`, then `02` will become an empty root, it'll point to nothing
        // and its data will be Data::default()
        let values = vec![0, 1];
        let hashes: Vec<Data> = values.into_iter().map(hash_from_u8).collect();

        let mut p = Pollard::new()
            .modify(hashes, vec![])
            .expect("Pollard should not fail");
        p.delete_single(2).expect("Node 2 should exist");
        assert_eq!(p.get_roots().len(), 1);
        let root = p.get_roots()[0].clone();
        assert_eq!(root, PolNode::default().into_rc());
    }
    #[test]
    fn test_delete_non_root() {
        // Assuming this tree, if we delete `01`, 00 will move up to 08's position
        // 14
        // |-----------------\
        // 12                13
        // |-------\         |--------\
        // 08       09       10       11
        // |----\   |----\   |----\   |----\
        // 00   01  02   03  04   05  06   07

        // 14
        // |-----------------\
        // 12                13
        // |-------\         |--------\
        // 08       09       10       11
        // |----\   |----\   |----\   |----\
        // 00   01  02   03  04   05  06   07

        // Where 08's data is just 00's

        let values = vec![0, 1, 2, 3, 4, 5, 6, 7];
        let hashes: Vec<Data> = values.into_iter().map(hash_from_u8).collect();

        let p = Pollard::new()
            .modify(hashes.clone(), vec![])
            .expect("Pollard should not fail")
            .modify(vec![], vec![1])
            .expect("Still should not fail");

        assert_eq!(p.roots.len(), 1);
        let (_, node, _) = p.grab_node(8).expect("This tree should have pos 8");
        assert_eq!(node.get_data(), hashes[0]);
    }
    #[derive(Debug, Deserialize)]
    struct TestCase {
        leaf_preimages: Vec<u8>,
        target_values: Option<Vec<u64>>,
        expected_roots: Vec<String>,
    }
    fn run_single_addition_case(case: TestCase) {
        let hashes = case
            .leaf_preimages
            .iter()
            .map(|preimage| hash_from_u8(*preimage))
            .collect();
        let p = Pollard::new()
            .modify(hashes, vec![])
            .expect("Test pollards are valid");
        assert_eq!(p.get_roots().len(), case.expected_roots.len());
        let expected_roots = case
            .expected_roots
            .iter()
            .map(|root| sha256::Hash::from_hex(root).unwrap())
            .collect::<Vec<_>>();
        let roots = p
            .get_roots()
            .iter()
            .map(|root| root.get_data())
            .collect::<Vec<_>>();
        assert_eq!(expected_roots, roots, "Test case failed {:?}", case);
    }
    fn run_case_with_deletion(case: TestCase) {
        let hashes = case
            .leaf_preimages
            .iter()
            .map(|preimage| hash_from_u8(*preimage))
            .collect();
        let dels = case
            .target_values
            .clone()
            .expect("Del test must have targets");
        let p = Pollard::new()
            .modify(hashes, vec![])
            .expect("Test pollards are valid")
            .modify(vec![], dels)
            .expect("still should be valid");

        assert_eq!(p.get_roots().len(), case.expected_roots.len());
        let expected_roots = case
            .expected_roots
            .iter()
            .map(|root| sha256::Hash::from_hex(root).unwrap())
            .collect::<Vec<_>>();
        let roots = p
            .get_roots()
            .iter()
            .map(|root| root.get_data())
            .collect::<Vec<_>>();
        assert_eq!(expected_roots, roots, "Test case failed {:?}", case);
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
    #[test]
    fn test() {
        let values = vec![0, 1, 2, 3, 4, 5, 6, 7];
        let hashes: Vec<Data> = values.into_iter().map(hash_from_u8).collect();

        let p = Pollard::new()
            .modify(hashes, vec![])
            .expect("Pollard should not fail")
            .modify(vec![], vec![0, 3])
            .expect("Still should not fail");
        println!("{:?}", p.get_roots()[0].get_data());
    }
}
