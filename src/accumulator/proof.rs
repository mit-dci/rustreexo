use crate::accumulator::{stump::Stump, types, util};
use bitcoin_hashes::sha256;

#[derive(Debug, Default)]
/// A proof is a collection of hashes and positions. Each target position
/// points to a leaf to be proven. Hashes are all
/// hashes that can't be calculated from the data itself.
/// Proofs are generated elsewhere.
pub struct Proof {
    /// Targets are the i'th of leaf locations to delete and they are the bottommost leaves.
    /// With the tree below, the Targets can only consist of one of these: 02, 03, 04.
    ///```!
    ///  // 06
    ///  // |-------\
    ///  // 04      05
    ///  // |---\   |---\
    ///  //         02  03
    /// ```
    targets: Vec<u64>,

    /// All the nodes in the tree that are needed to hash up to the root of
    /// the tree. Here, the root is 06. If Targets are [00, 01], then Proof
    /// would be [05] as you need 04 and 05 to hash to 06. 04 can be calculated
    /// by hashing 00 and 01.
    ///```!
    /// // 06  
    /// // |-------\
    /// // 04      05
    /// // |---\   |---\
    /// // 00  01  02  03
    /// ```
    hashes: Vec<sha256::Hash>,
}

impl Proof {
    /// Creates a proof from a vector of target and hashes.
    /// `targets` are u64s and indicates the position of the leafs we are
    /// trying to prove.
    /// `hashes` are of type `sha256::Hash` and are all hashes we need for computing the roots.
    ///
    /// Assuming a tree with leaf values [0, 1, 2, 3, 4, 5, 6, 7], we should see something like this:
    ///```!
    /// // 14
    /// // |-----------------\
    /// // 12                13
    /// // |---------\       |--------\
    /// // 08       09       10       11
    /// // |----\   |----\   |----\   |----\
    /// // 00   01  02   03  04   05  06   07
    /// ```
    /// If we are proving `00` (i.e. 00 is our target), then we need 01,
    /// 09 and 13's hashes, so we can compute 14 by hashing both siblings
    /// in each level (00 and 01, 08 and 09 and 12 and 13). Note that
    /// some hashes we can compute by ourselves, and are not present in the
    /// proof, in this case 00, 08, 12 and 14.
    /// # Example
    /// ```
    ///   use bitcoin_hashes::{sha256, Hash, HashEngine};
    ///   use rustreexo::accumulator::{proof::Proof};
    ///   let targets = vec![0];
    ///   
    ///   let mut proof_hashes = Vec::new();
    ///   let targets = vec![0];
    ///   // For proving 0, we need 01, 09 and 13's hashes. 00, 08, 12 and 14 can be calculated
    ///   //Fill `proof_hashes` up with all hashes
    ///   Proof::new(targets, proof_hashes);
    /// ```  
    pub fn new(targets: Vec<u64>, hashes: Vec<sha256::Hash>) -> Self {
        Proof {
            targets: targets,
            hashes: hashes,
        }
    }
    /// Public interface for verifying proofs. Returns a result with a bool or an Error
    /// True means the proof is true given the current stump, false means the proof is
    /// not valid given the current stump.
    ///# Examples
    /// ```
    ///   use bitcoin_hashes::{sha256::Hash as Sha256, Hash, HashEngine};
    ///   use std::str::FromStr;
    ///   use rustreexo::accumulator::{stump::Stump, proof::Proof};
    ///   let s = Stump::new();
    ///   // Creates a tree with those values as leafs
    ///   let test_values:Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7];
    ///   // Targets are nodes witch we intend to prove
    ///   let targets = vec![0];
    ///   
    ///   let mut proof_hashes = Vec::new();
    ///   // This tree will look like this
    ///   // 14
    ///   // |-----------------\
    ///   // 12                13
    ///   // |---------\       |--------\
    ///   // 08       09       10       11
    ///   // |----\   |----\   |----\   |----\
    ///   // 00   01  02   03  04   05  06   07
    ///   // For proving 0, we need 01, 09 and 13's hashes. 00, 08, 12 and 14 can be calculated
    ///   proof_hashes.push(Sha256::from_str("4bf5122f344554c53bde2ebb8cd2b7e3d1600ad631c385a5d7cce23c7785459a").unwrap());
    ///   proof_hashes.push(Sha256::from_str("9576f4ade6e9bc3a6458b506ce3e4e890df29cb14cb5d3d887672aef55647a2b").unwrap());
    ///   proof_hashes.push(Sha256::from_str("29590a14c1b09384b94a2c0e94bf821ca75b62eacebc47893397ca88e3bbcbd7").unwrap());
    ///
    ///   let mut hashes = Vec::new();
    ///   for i in test_values {
    ///       let mut engine = Sha256::engine();
    ///       engine.input(&[i]);
    ///       let hash = Sha256::from_engine(engine);
    ///       hashes.push(hash);
    ///   }
    ///   let s = s.modify(&hashes, &vec![], &Proof::default()).unwrap().0;
    ///   let p = Proof::new(targets, proof_hashes);
    ///   assert!(p.verify(&vec![hashes[0]] , &s).expect("This proof is valid"));
    ///```
    pub fn verify(&self, del_hashes: &Vec<sha256::Hash>, stump: &Stump) -> Result<bool, String> {
        if self.targets.len() == 0 {
            return Ok(true);
        }

        let mut calculated_roots = self
            .calculate_hashes(del_hashes, stump)?
            .1
            .into_iter()
            .peekable();

        let mut number_matched_roots = 0;

        for root in stump.roots.iter().rev() {
            if let Some(next_calculated_root) = calculated_roots.peek() {
                if *next_calculated_root == *root {
                    number_matched_roots += 1;
                    calculated_roots.next();
                }
            }
        }

        if calculated_roots.len() != number_matched_roots && calculated_roots.len() != 0 {
            return Ok(false);
        }
        Ok(true)
    }

    /// Returns how many targets this proof has
    pub fn targets(&self) -> usize {
        self.targets.len()
    }

    /// This function computes a set of roots from a proof.
    /// If some target's hashes are null, then it computes the roots after
    /// those targets are deleted. In this context null means [sha256::Hash::default].
    ///
    /// It's the caller's responsibility to null out the targets if desired by
    /// passing a `bitcoin_hashes::sha256::Hash::default()` instead of the actual hash.
    pub(crate) fn calculate_hashes(
        &self,
        del_hashes: &Vec<sha256::Hash>,
        stump: &Stump,
    ) -> Result<(Vec<(u64, sha256::Hash)>, Vec<sha256::Hash>), String> {
        // Where all the root hashes that we've calculated will go to.
        let total_rows = util::tree_rows(stump.leafs);

        // Where all the parent hashes we've calculated in a given row will go to.
        let mut calculated_root_hashes =
            Vec::<sha256::Hash>::with_capacity(util::num_roots(stump.leafs) as usize);

        // As we calculate nodes upwards, it accumulates here
        let mut nodes: Vec<_> = self
            .targets
            .to_owned()
            .into_iter()
            .zip(del_hashes.to_owned())
            .collect();

        // Nodes must be sorted for finding siblings during hashing
        nodes.sort();

        // An iterator over proof hashes
        let mut hashes_iter = self.hashes.iter();

        for row in 0..=total_rows {
            // An iterator that only contains nodes of the current row
            let mut row_nodes = nodes
                .to_owned()
                .into_iter()
                .filter(|x| util::detect_row(x.0, total_rows) == row)
                .peekable();

            while let Some((pos, hash)) = row_nodes.next() {
                let next_to_prove = util::parent(pos, total_rows);
                // If the current position is a root, we add that to our result and don't go any further
                if util::is_root_position(pos, stump.leafs, total_rows) {
                    calculated_root_hashes.push(hash);
                    continue;
                }

                if let Some((next_pos, next_hash)) = row_nodes.peek() {
                    // Is the next node our sibling? If so, we should be hashed together
                    if util::is_right_sibling(pos, *next_pos) {
                        // There are three possible cases: the current hash is null,
                        // and the sibling is present, we push the sibling to targets.
                        // If The sibling is null, we push the current node.
                        // If none of them is null, we compute the parent hash of both siblings
                        // and push this to the next target.
                        if hash == sha256::Hash::default() {
                            Proof::sorted_push(&mut nodes, (next_to_prove, *next_hash));
                        } else if *next_hash == sha256::Hash::default() {
                            Proof::sorted_push(&mut nodes, (next_to_prove, hash));
                        } else {
                            let hash = types::parent_hash(&hash, &next_hash);

                            Proof::sorted_push(&mut nodes, (next_to_prove, hash));
                        }

                        // Since we consumed 2 elements from nodes, skip one more here
                        // We need make this explicitly because peek, by definition
                        // does not advance the iterator.
                        row_nodes.next();

                        continue;
                    }
                }

                // If the next node is not my sibling, the hash must be passed inside the proof
                if let Some(next_proof_hash) = hashes_iter.next() {
                    if hash != sha256::Hash::default() {
                        let hash = if util::is_left_niece(pos) {
                            types::parent_hash(&hash, next_proof_hash)
                        } else {
                            types::parent_hash(next_proof_hash, &hash)
                        };

                        Proof::sorted_push(&mut nodes, (next_to_prove, hash));
                        continue;
                    } else {
                        // If none of the above, push a null hash upwards
                        Proof::sorted_push(&mut nodes, (next_to_prove, *next_proof_hash));
                    }
                } else {
                    return Err(String::from("Proof too short"));
                }
            }
        }

        Ok((nodes, calculated_root_hashes))
    }

    fn sorted_push(
        nodes: &mut Vec<(u64, bitcoin_hashes::sha256::Hash)>,
        to_add: (u64, bitcoin_hashes::sha256::Hash),
    ) {
        nodes.push(to_add);
        nodes.sort();
    }
}

#[cfg(test)]
mod tests {
    use std::str::FromStr;

    use bitcoin_hashes::{sha256, Hash, HashEngine};
    use serde::Deserialize;

    use super::Proof;
    use crate::accumulator::stump::Stump;
    #[derive(Deserialize)]
    struct TestCase {
        numleaves: usize,
        roots: Vec<String>,
        targets: Vec<u64>,
        target_preimages: Vec<u8>,
        proofhashes: Vec<String>,
        expected: bool,
    }
    fn hash_from_u8(value: u8) -> bitcoin_hashes::sha256::Hash {
        let mut engine = bitcoin_hashes::sha256::Hash::engine();

        engine.input(&[value]);

        sha256::Hash::from_engine(engine)
    }
    #[test]
    fn test_calculate_hashes() {
        // Tests if the calculated roots and nodes are correct.
        // The values we use to get some hashes
        let preimages = vec![0, 1, 2, 3, 4, 5, 6, 7];
        let hashes = preimages
            .into_iter()
            .map(|preimage| hash_from_u8(preimage))
            .collect();
        // Create a new stump with 8 leaves and 1 root
        let s = Stump::new()
            .modify(&hashes, &vec![], &Proof::default())
            .expect("This stump is valid")
            .0;

        // Nodes that will be deleted
        let del_hashes = vec![hashes[0], hashes[2], hashes[4], hashes[6]];
        let proof = vec![
            "4bf5122f344554c53bde2ebb8cd2b7e3d1600ad631c385a5d7cce23c7785459a",
            "084fed08b978af4d7d196a7446a86b58009e636b611db16211b65a9aadff29c5",
            "e77b9a9ae9e30b0dbdb6f510a264ef9de781501d7b6b92ae89eb059c5ab743db",
            "ca358758f6d27e6cf45272937977a748fd88391db679ceda7dc7bf1f005ee879",
        ];
        let proof_hashes = proof
            .into_iter()
            .map(|hash| bitcoin_hashes::sha256::Hash::from_str(hash).unwrap())
            .collect();

        let p = Proof::new(vec![0, 2, 4, 6], proof_hashes);

        // We should get those computed nodes...
        let expected_hashes = [
            "6e340b9cffb37a989ca544e6bb780a2c78901d3fb33738768511a30617afa01d",
            "dbc1b4c900ffe48d575b5da5c638040125f65db0fe3e24494b76ea986457d986",
            "e52d9c508c502347344d8c07ad91cbd6068afc75ff6292f062a09ca381c89e71",
            "67586e98fad27da0b9968bc039a1ef34c939b9b8e523a8bef89d478608c5ecf6",
            "02242b37d8e851f1e86f46790298c7097df06893d6226b7c1453c213e91717de",
            "9576f4ade6e9bc3a6458b506ce3e4e890df29cb14cb5d3d887672aef55647a2b",
            "9eec588c41d87b16b0ee226cb38da3864f9537632321d8be855a73d5616dcc73",
            "34028bbc87000c39476cdc60cf80ca32d579b3a0e2d3f80e0ad8c3739a01aa91",
            "df46b17be5f66f0750a4b3efa26d4679db170a72d41eb56c3e4ff75a58c65386",
            "29590a14c1b09384b94a2c0e94bf821ca75b62eacebc47893397ca88e3bbcbd7",
            "b151a956139bb821d4effa34ea95c17560e0135d1e4661fc23cedc3af49dac42",
        ];
        // ... at these positions ...
        let expected_pos = [0, 2, 4, 6, 8, 9, 10, 11, 12, 13, 14];

        // ... leading to this root
        let expected_roots = ["b151a956139bb821d4effa34ea95c17560e0135d1e4661fc23cedc3af49dac42"];

        let expected_roots: Vec<_> = expected_roots
            .iter()
            .map(|root| bitcoin_hashes::sha256::Hash::from_str(root).unwrap())
            .collect();

        let mut expected_computed = expected_hashes
            .iter()
            .map(|hash| bitcoin_hashes::sha256::Hash::from_str(hash).unwrap())
            .zip(&expected_pos);

        let calculated = p.calculate_hashes(&del_hashes, &s);

        // We don't expect any errors from this simple test
        assert!(calculated.is_ok());

        let (nodes, roots) = calculated.unwrap();

        // Make sure we got the expect roots
        assert_eq!(roots, expected_roots);

        // Did we compute all expected nodes?
        assert_eq!(nodes.len(), expected_computed.len());
        // For each calculated position, check if the position and hashes are as expected
        for (pos, hash) in nodes {
            if let Some((expected_hash, expected_pos)) = expected_computed.next() {
                assert_eq!(pos, *expected_pos as u64);
                assert_eq!(hash, expected_hash);
            } else {
                panic!()
            }
        }
    }
    fn run_single_case(case: &serde_json::Value) {
        let case = serde_json::from_value::<TestCase>(case.clone()).expect("Invalid test case");
        let roots = case
            .roots
            .into_iter()
            .map(|root| sha256::Hash::from_str(root.as_str()).expect("Test case hash is valid"))
            .collect();

        let s = Stump {
            leafs: case.numleaves as u64,
            roots,
        };

        let targets = case.targets;
        let del_hashes = case
            .target_preimages
            .into_iter()
            .map(|target| hash_from_u8(target))
            .collect();

        let proof_hashes = case
            .proofhashes
            .into_iter()
            .map(|hash| sha256::Hash::from_str(hash.as_str()).expect("Test case hash is valid"))
            .collect();

        let p = Proof::new(targets, proof_hashes);
        let expected = case.expected;

        let res = p.verify(&del_hashes, &s);
        assert!(Ok(expected) == res);
    }

    #[test]
    fn test_proof_verify() {
        let contents = std::fs::read_to_string("test_values/test_cases.json")
            .expect("Something went wrong reading the file");

        let values: serde_json::Value =
            serde_json::from_str(contents.as_str()).expect("JSON deserialization error");
        let tests = values["proof_tests"].as_array().unwrap();
        for test in tests {
            run_single_case(test);
        }
    }
}
