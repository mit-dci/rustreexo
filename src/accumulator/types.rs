// Rustreexo
use bitcoin_hashes::{sha256, Hash};

extern crate sha2;

use sha2::{Digest, Sha512_256};

// parent_hash return the merkle parent of the two passed in nodes
pub fn parent_hash(left: &sha256::Hash, right: &sha256::Hash) -> sha256::Hash {
    let hash = Sha512_256::new()
        .chain_update(left)
        .chain_update(right)
        .finalize();

    sha256::Hash::from_slice(hash.as_slice()).expect("parent_hash: Engines shouldn't be Err")
}

#[cfg(test)]
mod test {
    use bitcoin_hashes::{hex::ToHex, sha256, Hash, HashEngine};

    fn hash_from_u8(value: u8) -> sha256::Hash {
        let mut engine = bitcoin_hashes::sha256::Hash::engine();

        engine.input(&[value]);

        sha256::Hash::from_engine(engine)
    }
    #[test]
    fn test_parent_hash() {
        let hash1 = hash_from_u8(0);
        let hash2 = hash_from_u8(1);

        let parent_hash = super::parent_hash(&hash1, &hash2);

        assert_eq!(
            parent_hash.to_hex(),
            "02242b37d8e851f1e86f46790298c7097df06893d6226b7c1453c213e91717de"
        );
    }
}
