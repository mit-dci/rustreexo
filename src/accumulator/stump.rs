use super::{proof::Proof, types};
use bitcoin_hashes::sha256;
use std::vec;

#[derive(Debug, Clone, PartialEq)]
pub struct Stump {
    pub leafs: u64,
    pub roots: Vec<bitcoin_hashes::sha256::Hash>,
}

impl Stump {
    /// Creates an empty Stump
    ///# Example
    /// ```
    ///   use rustreexo::accumulator::stump::Stump;
    ///   let s = Stump::new();
    /// ```
    pub fn new() -> Self {
        Stump {
            leafs: 0,
            roots: Vec::new(),
        }
    }
    /// Modify is the external API to change the accumulator state. Since order
    /// matters, you can only modify, providing a list of utxos to be added,
    /// and txos to be removed, along with it's proof. Either may be
    /// empty.
    ///# Example
    /// ```
    ///   use rustreexo::accumulator::{stump::Stump, proof::Proof};
    ///   use bitcoin_hashes::sha256::Hash;
    ///   use std::str::FromStr;
    ///
    ///   let s = Stump::new();
    ///   let utxos = vec![Hash::from_str("b151a956139bb821d4effa34ea95c17560e0135d1e4661fc23cedc3af49dac42").unwrap()];
    ///   let stxos = vec![];
    ///   let s = s.modify(&utxos, &stxos, &Proof::default());
    ///   assert!(s.is_ok());
    ///   assert_eq!(s.unwrap().roots, utxos);
    /// ```
    pub fn modify(
        &self,
        utxos: &Vec<bitcoin_hashes::sha256::Hash>,
        del_hashes: &Vec<bitcoin_hashes::sha256::Hash>,
        proof: &Proof,
    ) -> Result<Stump, String> {
        let mut root_candidates = proof
            .calculate_hashes(del_hashes, self)?
            .1
            .into_iter()
            .rev()
            .peekable();
        let mut computed_roots = self.remove(del_hashes, proof)?.into_iter().rev();

        let mut new_roots = vec![];

        for root in self.roots.iter() {
            if let Some(root_candidate) = root_candidates.peek() {
                if *root_candidate == *root {
                    if let Some(new_root) = computed_roots.next() {
                        new_roots.push(new_root);
                        root_candidates.next();
                        continue;
                    }
                }
            }

            new_roots.push(*root);
        }

        let roots = Stump::add(new_roots, utxos, self.leafs);

        Ok(Stump {
            leafs: self.leafs + utxos.len() as u64,
            roots: roots,
        })
    }

    /// Rewinds old tree state, this should be used in case of reorgs.
    /// Takes the ownership over `old_state`.
    ///# Example
    /// ```
    ///   use rustreexo::accumulator::{stump::Stump, proof::Proof};
    ///   let s_old = Stump::new();
    ///   let mut s_new = Stump::new();
    ///
    ///   let s_old = s_old.modify(&vec![], &vec![], &Proof::default()).unwrap();
    ///   s_new = s_old.clone();
    ///   s_new = s_new.modify(&vec![], &vec![], &Proof::default()).unwrap();
    ///
    ///   // A reorg happened
    ///   s_new.undo(s_old);
    ///```
    pub fn undo(&mut self, old_state: Stump) {
        self.leafs = old_state.leafs;
        self.roots = old_state.roots;
    }

    fn remove(
        &self,
        del_hashes: &Vec<bitcoin_hashes::sha256::Hash>,
        proof: &Proof,
    ) -> Result<Vec<bitcoin_hashes::sha256::Hash>, String> {
        if del_hashes.len() == 0 {
            return Ok(self.roots.clone());
        }

        let del_hashes = vec![sha256::Hash::default(); proof.targets()];
        let (_, new_roots) = proof.calculate_hashes(&del_hashes, self)?;

        Ok(new_roots)
    }
    /// Adds new leafs into the root
    fn add(
        mut roots: Vec<bitcoin_hashes::sha256::Hash>,
        utxos: &Vec<bitcoin_hashes::sha256::Hash>,
        mut leafs: u64,
    ) -> Vec<bitcoin_hashes::sha256::Hash> {
        for i in utxos.iter() {
            Stump::add_single(&mut roots, *i, leafs);
            leafs += 1;
        }

        roots
    }

    fn add_single(
        roots: &mut Vec<bitcoin_hashes::sha256::Hash>,
        node: bitcoin_hashes::sha256::Hash,
        leafs: u64,
    ) {
        let mut h = 0;
        // Iterates over roots, if we find a root that is not empty, we concatenate with
        // the one we are adding and create new root, leaving this position empty. Stops
        // when find an empty root.

        // You can say if a root is empty, by looking a the binary representations of the
        // number of leafs. If the h'th bit is one, then this position is occupied, empty
        // otherwise.
        let mut to_add = node;
        while (leafs >> h) & 1 == 1 {
            let root = roots.pop();
            if let Some(root) = root {
                to_add = types::parent_hash(&root, &to_add);
            }
            h += 1;
        }

        roots.push(to_add);
    }
}

#[cfg(test)]
mod test {
    use crate::{
        accumulator::proof::Proof, get_hash_array_from_obj, get_json_field, get_u64_array_from_obj,
    };

    use super::Stump;
    use bitcoin_hashes::{hex::ToHex, sha256, Hash, HashEngine};
    use std::{str::FromStr, vec};

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

    fn run_case_with_deletion(case: &serde_json::Value) {
        let leafs = get_json_field!("leaf_values", case);
        let target_values = get_json_field!("target_values", case);
        let roots = get_json_field!("roots", case);
        let proof_hashes = get_json_field!("proof_hashes", case);

        let leafs = get_u64_array_from_obj!(leafs);
        let target_values = get_u64_array_from_obj!(target_values);
        let roots = get_hash_array_from_obj!(roots);
        let proof_hashes = get_hash_array_from_obj!(proof_hashes);

        let mut leaf_hashes = vec![];
        for i in leafs.iter() {
            leaf_hashes.push(hash_from_u8(*i as u8));
        }

        let mut target_hashes = vec![];
        for i in target_values.iter() {
            target_hashes.push(hash_from_u8(*i as u8));
        }

        let proof = Proof::new(target_values, proof_hashes);

        let stump = Stump::new()
            .modify(&leaf_hashes, &vec![], &Proof::default())
            .expect("This stump is valid");

        let stump = stump.modify(&vec![], &target_hashes, &proof).unwrap();

        assert_eq!(stump.roots, roots);
    }

    fn run_single_addition_case(case: &serde_json::Value) {
        let s = Stump::new();
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

        let s = s
            .modify(&hashes, &vec![], &Proof::default())
            .expect("Stump from test cases are valid");

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

        let s_old = Stump::new();
        let s_old = s_old
            .modify(&hashes, &vec![], &Proof::default())
            .expect("Stump from test cases are valid");

        let mut s_new = s_old.clone();

        // Add 100 more UTXOS
        for i in 0..100 as u8 {
            hashes.push(hash_from_u8(i));
        }

        s_new
            .modify(&hashes, &vec![], &Proof::default())
            .expect("Stump from test cases are valid");
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
        let insertion_tests = values["insertion_tests"].as_array().unwrap();
        let deletion_tests = values["deletion_tests"].as_array().unwrap();

        for i in insertion_tests {
            run_single_addition_case(i);
        }
        for i in deletion_tests {
            run_case_with_deletion(i);
        }
    }
}
