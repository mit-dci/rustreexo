use super::types;

#[derive(Debug, Clone, PartialEq)]
pub struct Stump {
    leafs: u64,
    roots: Vec<bitcoin_hashes::sha256::Hash>,
}

impl Stump {
    /// Creates an empty Stump
    pub fn new() -> Self {
        Stump {
            leafs: 0,
            roots: Vec::new(),
        }
    }
    /// Modify is the external API to change the accumulator state. Since order
    /// matters, you can only modify, providing a list of utxos to be added,
    /// and txos (@TODO) to be removed, along with it's proof. Either may be
    /// empty.
    ///# Example
    /// ```
    ///   use rustreexo::accumulator::stump::Stump;
    ///   let mut s = Stump::new();
    ///   let utxos = vec![];
    ///   let stxos = vec![];
    ///   s.modify(&utxos, &stxos);
    /// ```
    pub fn modify(&mut self, utxos: &Vec<bitcoin_hashes::sha256::Hash>, _stxos: &Vec<u64>) {
        //remove
        self.add(utxos);
    }

    /// Rewinds old tree state, this should be used in case of reorgs.
    /// Takes the ownership over `old_state`.
    ///# Example
    /// ```
    ///   use rustreexo::accumulator::stump::Stump;
    ///   let mut s_old = Stump::new();
    ///   let mut s_new = Stump::new();
    ///   
    ///   s_old.modify(&vec![], &vec![]);
    ///   s_new = s_old.clone();
    ///   s_new.modify(&vec![], &vec![]);
    ///   
    ///   // A reorg happened
    ///   
    ///   s_new.undo(s_old);  
    ///```
    pub fn undo(&mut self, old_state: Stump) {
        self.leafs = old_state.leafs;
        self.roots = old_state.roots;
    }

    /// Adds new leafs into the root
    fn add(&mut self, utxos: &Vec<bitcoin_hashes::sha256::Hash>) {
        for i in utxos.iter() {
            self.add_single(*i);
        }
    }

    fn add_single(&mut self, node: bitcoin_hashes::sha256::Hash) {
        let mut h = 0;
        // Iterates over roots, if we find a root that is not empty, we concatenate with
        // the one we are adding and create new root, leaving this position empty. Stops
        // when find an empty root.

        // You can say if a root is empty, by looking a the binary representations of the
        // number of leafs. If the h'th bit is one, then this position is occupied, empty
        // otherwise.
        let mut to_add = node;
        while (self.leafs >> h) & 1 == 1 {
            let root = self.roots.pop();
            if let Some(root) = root {
                to_add = types::parent_hash(&root, &to_add);
            }
            h += 1;
        }

        self.roots.push(to_add);

        self.leafs += 1;
    }
}

#[cfg(test)]
mod test {
    use super::Stump;
    use bitcoin_hashes::{hex::ToHex, sha256, Hash, HashEngine};
    use std::vec;

    #[test]
    // Make a few simple tests about stump creation
    fn test_stump() {
        let s = Stump::new();
        assert!(s.leafs == 0);
        assert!(s.roots.len() == 0);
    }

    fn hash_from_u8(value: u8) -> sha256::Hash {
        let mut engine = bitcoin_hashes::sha256::Hash::engine();

        engine.input(&[value]);

        sha256::Hash::from_engine(engine)
    }

    fn run_single_case(case: &serde_json::Value) {
        let mut s = Stump::new();
        let test_values = case["leaf_values"]
            .as_array()
            .expect("Test data is missing");

        let roots = case["roots"]
            .as_array()
            .expect("Fail reading roots for this case");

        let mut hashes = vec![];

        for i in test_values {
            hashes.push(hash_from_u8(i.as_u64().unwrap() as u8));
        }

        s.modify(&hashes, &vec![]);

        assert_eq!(s.leafs, hashes.len() as u64);

        for i in 0..roots.len() {
            assert_eq!(roots[i].as_str().unwrap(), s.roots[i].to_hex());
        }
    }

    #[test]
    fn test_undo() {
        let mut hashes = vec![];
        // Add 100 initial UTXOs
        for i in 0..100 as u8 {
            hashes.push(hash_from_u8(i));
        }

        let mut s_old = Stump::new();
        s_old.modify(&hashes, &vec![]);

        let mut s_new = s_old.clone();

        // Add 100 more UTXOS
        for i in 0..100 as u8 {
            hashes.push(hash_from_u8(i));
        }

        s_new.modify(&hashes, &vec![]);
        let s_old_copy = s_old.clone();

        // A reorg happened, need to roll back state
        s_new.undo(s_old);

        assert!(s_new == s_old_copy);
    }
    #[test]
    fn run_test_cases() {
        let contents = std::fs::read_to_string("test_values/test_cases.json")
            .expect("Something went wrong reading the file");

        let values: serde_json::Value =
            serde_json::from_str(contents.as_str()).expect("JSON deserialization error");
        let tests = values["insertion_tests"].as_array().unwrap();

        for i in tests {
            run_single_case(i);
        }
    }
}
