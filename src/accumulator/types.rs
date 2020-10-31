// Rustreexo

//use sha2::{Digest, Sha256};

use bitcoin::blockdata::transaction;
use bitcoin::hashes::{sha256, Hash, HashEngine};

type HASH = [u8; 32];

/// Leaf represents a utxo in the utreexo tree. These are the bottommost
/// nodes in the tree.
pub struct Leaf {
    ///  The hash representation of the Leaf
    pub hash: sha256::Hash,

    /// Remember is whether or not the UTXO this Leaf represents should
    /// be cached or not.
    pub remember: bool,
}

/// LeafData is all the data that goes into the hashing the leaf.
/// The data included is needed for transaction script validation.
/// The rest of the data is for hardening against hash collisions.
pub struct LeafData {
    block_header: HASH,
    outpoint: transaction::OutPoint,
    height: i32,
    is_coinbase: bool,
    amt: i64,
    pk_script: Vec<u8>,
}

/// Arrow is used to describe the movement of a leaf to a different
/// position. This is used for batch deletions during removal
#[derive(Clone, Copy)]
#[derive(Debug)]
pub struct Arrow {
    pub from: u64,
    pub to: u64,
}

// parent_hash return the merkle parent of the two passed in nodes
pub fn parent_hash(left: &sha256::Hash, right: &sha256::Hash) -> sha256::Hash {
    let mut engine = bitcoin_hashes::sha256::Hash::engine();

    engine.input(left);
    engine.input(right);

    return sha256::Hash::from_engine(engine);
}
