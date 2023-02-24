use crate::{get_slice_const, CHash, Error};
use bitcoin_hashes::{sha256, Hash, HashEngine};

#[repr(C)]
#[derive(Debug, Clone)]
pub struct OutPoint {
    pub hash: CHash,
    pub index: u32,
}
#[repr(C)]
#[derive(Debug, Clone)]
pub struct TxOut {
    pub value: u64,
    pub spk_len: usize,
    pub script_pubkey: *const u8,
}

#[repr(C)]
/// Leaf data is the data that is hashed when adding to utreexo state. It contains validation
/// data and some commitments to make it harder to attack an utreexo-only node.
#[derive(Debug, Clone)]
pub struct LeafData {
    /// A commitment to the block creating this utxo
    pub block_hash: CHash,
    /// The utxo's outpoint
    pub prevout: OutPoint,
    /// Header code is a compact commitment to the block height and whether or not this
    /// transaction is coinbase. It's defined as
    ///
    /// ```
    /// header_code: u32 = if transaction.is_coinbase() {
    ///     (block_height << 1 ) | 1
    /// } else {
    ///     block_height << 1
    /// };
    /// ```
    pub header_code: u32,
    /// The actual utxo
    pub utxo: TxOut,
}

impl LeafData {
    pub fn new(block_hash: CHash, prevout: OutPoint, header_code: u32, utxo: TxOut) -> Self {
        Self {
            block_hash,
            prevout,
            header_code,
            utxo,
        }
    }
    #[no_mangle]
    pub fn leaf_hash(&self) -> CHash {
        let mut engine = sha256::Hash::engine();
        engine.input(&*self.block_hash);
        engine.input(&*self.prevout.hash);
        engine.input(&self.prevout.index.to_le_bytes());
        engine.input(&self.header_code.to_le_bytes());
        engine.input(&self.utxo.value.to_le_bytes());
        let spk = get_slice_const(self.utxo.script_pubkey, self.utxo.spk_len);
        engine.input(spk);
        CHash(sha256::Hash::from_engine(engine).into_inner())
    }
}

#[no_mangle]
pub unsafe extern "C" fn rustreexo_leaf_hash(
    errno: *mut Error,
    hash: *mut CHash,
    leaf: LeafData,
) -> usize {
    check_ptr!(errno);
    check_ptr!(errno, hash);
    unsafe { hash.write(leaf.leaf_hash()) };
    crate::EXIT_SUCCESS
}
