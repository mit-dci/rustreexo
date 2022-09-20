use bitcoin_hashes::sha256::Hash;
use std::fmt::Debug;
#[allow(unused)]
use std::{
    cell::{Cell, RefCell},
    mem::{self, swap},
    rc::{Rc, Weak},
};

use super::types;
type Node = Rc<PolNode>;

#[derive(Clone)]
pub struct PolNode {
    data: Hash,
    aunt: Option<Node>,
    l_niece: RefCell<Option<Node>>,
    r_niece: RefCell<Option<Node>>,
}

impl Debug for PolNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.data)
    }
}

impl PolNode {
    fn new(
        data: Hash,
        aunt: Option<Node>,
        l_niece: Option<Node>,
        r_niece: Option<Node>,
    ) -> PolNode {
        PolNode {
            data,
            aunt,
            l_niece: RefCell::new(l_niece),
            r_niece: RefCell::new(r_niece),
        }
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
            data,
            aunt,
            l_niece: RefCell::new(l_niece),
            r_niece: RefCell::new(r_niece),
        };

        node.as_rc()
    }
    /// Returns the current node as an Reference Counted Container "[Rc]". This is how
    /// nodes are stored inside the tree.
    fn as_rc(self) -> Node {
        Rc::new(self)
    }

    fn set_aunt(&self, aunt: Option<Node>) -> PolNode {
        PolNode {
            data: self.data,
            aunt,
            l_niece: self.clone().l_niece,
            r_niece: self.clone().r_niece,
        }
    }
    fn set_nieces(&self, l_niece: Option<Node>, r_niece: Option<Node>) {
        self.l_niece.replace(l_niece);
        self.r_niece.replace(r_niece);
    }
    fn chop(&self) {
        self.l_niece.replace(None);
        self.r_niece.replace(None);
    }
}
#[derive(Clone)]
pub struct Pollard {
    leaves: usize,
    roots: Vec<Node>,
}
impl Pollard {
    pub fn modify(&self, utxos: Vec<Hash>, _stxos: Vec<Hash>) {
        let roots = self.roots.clone();
        let _roots = Pollard::add(roots, utxos, self.leaves);
    }

    fn add(mut roots: Vec<Node>, utxos: Vec<Hash>, mut num_leaves: usize) -> Vec<Node> {
        for utxo in utxos {
            roots = Pollard::add_single(roots, utxo, num_leaves);
            num_leaves += 1;
        }

        roots
    }

    fn add_single(mut roots: Vec<Node>, node: Hash, mut num_leaves: usize) -> Vec<Node> {
        let mut node = PolNode::new(node, None, None, None).as_rc();

        while num_leaves & 1 == 1 {
            // If num_leaves & 1 == 1, roots cannot be None
            let left_root = roots.pop().unwrap();

            left_root.l_niece.swap(&node.l_niece);
            left_root.r_niece.swap(&node.r_niece);

            let n_hash = types::parent_hash(&left_root.data.clone(), &node.data.clone());
            let new_node = PolNode::new_node(n_hash, None, None, None);

            let left_niece = left_root.set_aunt(Some(new_node.clone())).as_rc();
            let right_niece = node.set_aunt(Some(new_node.clone())).as_rc();

            new_node.set_nieces(Some(left_niece), Some(right_niece));
            node = new_node;

            // left_root.aunt = new_node.clone();
            num_leaves >>= 1;
        }

        roots.push(node);
        roots
    }
}

mod test {
    use super::{PolNode, Pollard};
    use bitcoin_hashes::{sha256::Hash as Data, Hash, HashEngine};
    fn hash_from_u8(value: u8) -> Data {
        let mut engine = Data::engine();

        engine.input(&[value]);

        Hash::from_engine(engine)
    }

    #[test]
    fn test_add() {
        let values = vec![0, 1, 2, 3, 4, 5, 6, 7];
        let hashes = values.into_iter().map(|val| hash_from_u8(val)).collect();

        let roots = Pollard::add(vec![], hashes, 0);
        assert_eq!(
            "b151a956139bb821d4effa34ea95c17560e0135d1e4661fc23cedc3af49dac42",
            roots[0].data.to_string().as_str(),
        );
    }
}
