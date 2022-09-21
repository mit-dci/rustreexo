use bitcoin_hashes::{hex::ToHex, sha256::Hash};
use std::{
    borrow::Borrow,
    fmt::{write, Debug},
};
#[allow(unused)]
use std::{
    cell::{Cell, RefCell},
    mem::{self, swap},
    rc::{Rc, Weak},
};

use crate::accumulator::util::detect_row_hashes;

use super::{
    types::{self, parent_hash},
    util::{detect_row, is_left_niece, next_pow2, num_roots, parent, tree_rows},
};
type Node = Rc<PolNode>;

#[derive(Clone, PartialEq, Eq, Default)]
pub struct PolNode {
    data: Hash,
    aunt: Option<Node>,
    l_niece: RefCell<Option<Node>>,
    r_niece: RefCell<Option<Node>>,
}

impl Debug for PolNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "\n{}\n|------\\\n", &self.data[0..2].to_hex())?;
        let (left_children, right_children) = self.get_children();

        if let Some(left_children) = left_children {
            write!(f, "{}   ", &left_children.data[0..2].to_hex())?;
        }
        if let Some(right_children) = right_children {
            write!(f, "{}\n", &right_children.data[0..2].to_hex())?;
        }
        Ok(())
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
    fn get_children(&self) -> (Option<Node>, Option<Node>) {
        let parent = self.get_parent();
        if let Some(parent) = parent {
            // I'm the left children, so my sibling is the right one
            if parent.get_l_niece().unwrap_or_default().as_ref().eq(self) {
                if let Some(sibling) = parent.get_r_niece() {
                    return (sibling.get_l_niece(), sibling.get_r_niece());
                }
            } else {
                if let Some(sibling) = parent.get_l_niece() {
                    return (sibling.get_l_niece(), sibling.get_r_niece());
                }
            }
        } else {
            return (self.get_l_niece(), self.get_r_niece());
        }
        // This means I'm a root,
        (None, None)
    }
    fn get_parent(&self) -> Option<Node> {
        //I'm a root, so no parent
        if let None = self.aunt {
            return None;
        }

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
    fn set_self_hash(&self, new: Node) {
        if let Some(aunt) = self.get_aunt() {
            if *aunt.get_l_niece().unwrap_or_default() == *self {
                aunt.l_niece.replace(Some(new));
            } else {
                aunt.r_niece.replace(Some(new));
            }
        }
    }
    fn recompute_parent_hash(&self) -> Result<Node, String> {
        if let (Some(l_niece), Some(r_niece)) = (self.get_l_niece(), self.get_r_niece()) {
            let new_parent_hash = parent_hash(&l_niece.data, &r_niece.data);
            let aunt = self.get_aunt();
            let new_node =
                PolNode::new(new_parent_hash, aunt.clone(), Some(l_niece), Some(r_niece));
            if let Some(aunt) = aunt {
                self.set_self_hash(new_node.as_rc());
                return aunt.recompute_parent_hash();
            } else {
                return Ok(new_node.as_rc());
            }
        }

        Ok(self.clone().as_rc())
    }
    fn get_aunt(&self) -> Option<Node> {
        self.aunt.clone()
    }
    fn get_l_niece(&self) -> Option<Node> {
        self.l_niece.borrow().clone()
    }
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
    leaves: u64,
    roots: Vec<Node>,
}

impl Pollard {
    pub fn new() -> Pollard {
        Pollard {
            leaves: 0,
            roots: vec![],
        }
    }
    pub fn modify(&self, utxos: Vec<Hash>, _stxos: Vec<u64>) -> Pollard {
        let utxos_after_deletion = self.leaves + utxos.len() as u64;
        let roots = self.roots.clone();
        let roots = Pollard::add(roots, utxos, self.leaves);

        Pollard {
            leaves: utxos_after_deletion,
            roots,
        }
    }

    /// Deletes a single node from a Pollard. The algorithm works as follows:
    /// Grab a node, it's sibling and it's parent.
    /// (i) if I'm deleting the node, but not it's sibling, then the sibling takes the parent's position
    /// (ii) if both are being deleted, then the parent is also deleted
    /// (iii) if my parent is a root, then the node's sibling becomes a root
    /// (iv) if I'm a root myself, then this root becomes an empty root (PolNode::Default).
    fn delete_single(&self, pos: u64) -> Result<Vec<Node>, String> {
        // Grab the node we'll move up
        let (from_node, _, to_node) = self.grab_node(pos)?;
        // What is the position of our parent?
        let parent_pos = parent(pos, tree_rows(self.leaves));
        // In what subtree we are?
        let (tree, _, _) = super::util::detect_offset(pos, self.leaves);
        let mut roots = self.roots.clone();

        // If the position I'm moving to has an aunt, I'm not becoming a root.
        if let Some(new_aunt) = &to_node.aunt {
            from_node.chop();
            println!("To node:{:?}", new_aunt);

            let new_node = from_node.set_aunt(Some(new_aunt.clone()));
            if is_left_niece(parent_pos) {
                new_aunt.l_niece.replace(Some(new_node.as_rc()));
            } else {
                new_aunt.r_niece.replace(Some(new_node.as_rc()));
            }
            
            roots[tree as usize] = roots[tree as usize].recompute_parent_hash()?;
        } else {
            // If it does not have a aunt, then I'm becoming a root
            let from_node = from_node.set_aunt(None).as_rc();
            roots[tree as usize] = from_node;
        }

        Ok(roots)
    }
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
        Err("node not found".to_string())
    }
    fn add(mut roots: Vec<Node>, utxos: Vec<Hash>, mut num_leaves: u64) -> Vec<Node> {
        for utxo in utxos {
            roots = Pollard::add_single(roots, utxo, num_leaves);
            num_leaves += 1;
        }

        roots
    }

    fn add_single(mut roots: Vec<Node>, node: Hash, mut num_leaves: u64) -> Vec<Node> {
        let mut node = PolNode::new(node, None, None, None).as_rc();

        while num_leaves & 1 == 1 {
            // If num_leaves & 1 == 1, roots cannot be None
            let left_root = roots
                .pop()
                .expect("add_single: num_leaves & 1 == 1 and no roots?");

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

impl std::fmt::Display for Pollard {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let trees = num_roots(self.leaves);
        let rows = tree_rows(self.leaves) + 1;
        let total_nodes = (2 as u64).pow(rows.into()) - 2;
        let mut pos = total_nodes - 1;
        for row in (0..=(rows - 1)).rev() {
            while detect_row(pos, rows - 1) == row {
                if let Ok((_, node, _)) = self.grab_node(pos.into()) {
                    write!(f, "{:?}", &node.data[0..2].to_hex())?;
                } else {
                    write!(f, "--")?;
                }
                if pos == 0 {
                    break;
                }
                pos -= 1;
            }
            write!(f, "\n")?;
        }
        // for row in (0..=rows).rev() {
        //     for node in start_node..end_node {

        //     }

        // }

        Ok(())
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
    fn test_grab_aunt() {
        let values = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14];
        let hashes = values.into_iter().map(|val| hash_from_u8(val)).collect();

        let p = Pollard::new().modify(hashes, vec![]);
        let node = p.grab_node(13);

        assert!(node.is_ok());

        let hash = node.unwrap().1.data;
        assert_eq!(
            hash.to_string().as_str(),
            "9d1e0e2d9459d06523ad13e28a4093c2316baafe7aec5b25f30eba2e113599c4"
        );
    }
    #[test]
    fn test_recompute_hashes() {
        let values = vec![0, 1, 2, 3];
        let hashes = values.into_iter().map(|val| hash_from_u8(val)).collect();

        let p = Pollard::new().modify(hashes, vec![]);
        let node = p.grab_node(0);
        if let Ok((_, _, parent)) = node {
            let res = parent.recompute_parent_hash();
            println!("{:?}", res);
        }
    }

    #[test]
    fn test_delete() {
        let values = vec![0, 1, 2, 3, 4, 5, 6, 7];
        let hashes = values.into_iter().map(|val| hash_from_u8(val)).collect();

        let p = Pollard::new().modify(hashes, vec![]);
        let roots = p.delete_single(0).expect("msg");

        println!("{:?}", roots);
    }
    #[test]
    fn test_add() {
        let values = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14];
        let hashes = values.into_iter().map(|val| hash_from_u8(val)).collect();

        let roots = Pollard::add(vec![], hashes, 0);

        assert_eq!(
            "b151a956139bb821d4effa34ea95c17560e0135d1e4661fc23cedc3af49dac42",
            roots[0].data.to_string().as_str(),
        );
        assert_eq!(
            "9c053db406c1a077112189469a3aca0573d3481bef09fa3d2eda3304d7d44be8",
            roots[1].data.to_string().as_str(),
        );
        assert_eq!(
            "55d0a0ef8f5c25a9da266b36c0c5f4b31008ece82df2512c8966bddcc27a66a0",
            roots[2].data.to_string().as_str(),
        );
        assert_eq!(
            "4d7b3ef7300acf70c892d8327db8272f54434adbc61a4e130a563cb59a0d0f47",
            roots[3].data.to_string().as_str(),
        );
    }
}
