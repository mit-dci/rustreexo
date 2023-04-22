// Rustreexo
use bitcoin_hashes::{sha512_256, Hash, HashEngine};

// parent_hash return the merkle parent of the two passed in nodes
pub fn parent_hash(left: &sha512_256::Hash, right: &sha512_256::Hash) -> sha512_256::Hash {
    let mut hash = sha512_256::Hash::engine();
    hash.input(left.as_byte_array());
    hash.input(right.as_byte_array());
    sha512_256::Hash::from_engine(hash)
}

#[cfg(test)]
mod test {
    use bitcoin_hashes::{sha256, sha512_256, Hash, HashEngine};

    fn hash_from_u8(value: u8) -> sha512_256::Hash {
        let mut engine = bitcoin_hashes::sha256::Hash::engine();

        engine.input(&[value]);

        sha512_256::Hash::from_slice(sha256::Hash::from_engine(engine).as_byte_array()).unwrap()
    }
    #[test]
    fn test_parent_hash() {
        let hash1 = hash_from_u8(0);
        let hash2 = hash_from_u8(1);

        let parent_hash = super::parent_hash(&hash1, &hash2);
        println!("{}", parent_hash.to_string().as_str());
        assert_eq!(
            parent_hash.to_string().as_str(),
            "02242b37d8e851f1e86f46790298c7097df06893d6226b7c1453c213e91717de"
        );
    }
}
