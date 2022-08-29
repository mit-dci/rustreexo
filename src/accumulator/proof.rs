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
    /// 14
    /// |-----------------\                               
    /// 12                13                         
    /// |---------\       |--------\               
    /// 08       09       10       11         
    /// |----\   |----\   |----\   |----\       
    /// 00   01  02   03  04   05  06   07
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
    ///   use bitcoin_hashes::{sha256, Hash, HashEngine};
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
    ///   proof_hashes.push(bitcoin_hashes::sha256::Hash::from_str("4bf5122f344554c53bde2ebb8cd2b7e3d1600ad631c385a5d7cce23c7785459a").unwrap());
    ///   proof_hashes.push(bitcoin_hashes::sha256::Hash::from_str("9576f4ade6e9bc3a6458b506ce3e4e890df29cb14cb5d3d887672aef55647a2b").unwrap());
    ///   proof_hashes.push(bitcoin_hashes::sha256::Hash::from_str("29590a14c1b09384b94a2c0e94bf821ca75b62eacebc47893397ca88e3bbcbd7").unwrap());
    ///   
    ///   let mut hashes = Vec::new();
    ///   for i in test_values {
    ///     let mut engine = bitcoin_hashes::sha256::Hash::engine();
    ///      engine.input(&[i]);
    ///      let hash = sha256::Hash::from_engine(engine);
    ///     hashes.push(hash);
    ///   }
    ///
    ///   let s = s.modify(&hashes, &vec![], &Proof::default()).unwrap();
    ///   let p = Proof::new(targets, proof_hashes);
    ///   assert!(p.verify(&vec![hashes[0]] , &s).expect("No error should happens"));
    ///```
    pub fn verify(&self, del_hashes: &Vec<sha256::Hash>, stump: &Stump) -> Result<bool, String> {
        if self.targets.len() == 0 {
            return Ok(true);
        }

        let mut calculated_roots = self
            .create_root_candidates(del_hashes, stump)?
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
    pub fn proof_after_deletion(
        &self,
        num_leafs: u64,
    ) -> Result<(Vec<bitcoin_hashes::sha256::Hash>, Proof), String> {
        let total_rows = util::tree_rows(num_leafs);
        let mut targets = self.targets.to_owned();
        targets.sort();

        let proof_positions = util::get_proof_positions(&targets, num_leafs, total_rows);

        let mut proof_hashes: Vec<_> = proof_positions
            .to_owned()
            .into_iter()
            .zip(self.hashes.to_owned())
            .collect();

        let mut targets: Vec<_> = util::detwin(targets.to_owned(), total_rows)
            .into_iter()
            .rev()
            .collect();

        // Here is where our modified proof will be constructed
        let mut target_hashes: Vec<(u64, bitcoin_hashes::sha256::Hash)> = vec![];

        // For each of the targets, we'll try to find the sibling in the proof hashes
        // and promote it as the parent. If it's not in the proof hashes, we'll move
        // the descendants of the existing targets and proofs of the sibling's parent
        // up by one row.

        while let Some(target) = targets.pop() {
            if util::is_root_position(target, num_leafs, total_rows) {
                target_hashes.push((target, bitcoin_hashes::sha256::Hash::default()));
                continue;
            }

            let sib = target ^ 1;
            // Is the node sibling on hash proofs?
            if let Some(idx) = proof_hashes.iter().position(|(pos, _)| sib == *pos) {
                let parent_pos = util::parent(sib as u64, total_rows);

                target_hashes.push((parent_pos, proof_hashes[idx].1));

                // Delete the sibling from proof_hashes as this sibling is a target now, not a proof.
                proof_hashes.remove(idx);
            } else {
                // If the sibling is not in the proof hashes or the targets,
                // the descendants of the sibling will be moving up.
                //
                // 14
                // |---------------\
                // 12              13
                // |-------\       |-------\
                // 08      09      10      11
                // |---\   |---\   |---\   |---\
                // 00  01          04  05  06  07

                let to_update: Vec<_> = target_hashes
                    .iter_mut()
                    .filter(|(node, _)| {
                        let parent = util::parent(sib, total_rows);
                        util::is_ancestor(parent, *node, total_rows).unwrap_or(false)
                    })
                    .collect();

                for to_update_node in to_update {
                    let new_pos = util::calc_next_pos(to_update_node.0, sib, total_rows)?;
                    to_update_node.0 = new_pos;
                }

                let to_update: Vec<_> = proof_hashes
                    .iter_mut()
                    .filter(|(node, _)| {
                        let parent = util::parent(sib, total_rows);
                        util::is_ancestor(parent, *node, total_rows).unwrap_or(false)
                    })
                    .collect();

                for node_to_update in to_update {
                    let next_pos = util::calc_next_pos(node_to_update.0, sib, total_rows)?;
                    node_to_update.0 = next_pos;
                }
            }
        }
        let mut new_proof_hashes = vec![];
        let mut new_target_hashes = vec![];

        proof_hashes.sort();
        target_hashes.sort();

        proof_hashes
            .iter()
            .for_each(|(_, hash)| new_proof_hashes.push(hash.to_owned()));
        let mut prove_targets = vec![];
        target_hashes.into_iter().for_each(|(pos, hash)| {
            prove_targets.push(pos);
            new_target_hashes.push(hash)
        });

        prove_targets.dedup();

        Ok((
            new_target_hashes,
            Proof {
                targets: prove_targets,
                hashes: new_proof_hashes,
            },
        ))
    }
    pub fn create_root_candidates(
        &self,
        del_hashes: &Vec<sha256::Hash>,
        stump: &Stump,
    ) -> Result<Vec<sha256::Hash>, String> {
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
                // If the current position is a root, we add that to our result and don't go any further
                if util::is_root_position(pos, stump.leafs, total_rows) {
                    calculated_root_hashes.push(hash);
                    continue;
                }

                if let Some((next_pos, next_hash)) = row_nodes.peek() {
                    // Is the next node our sibling? If so, we should be hashed together
                    if util::is_right_sibling(pos, *next_pos) {
                        let hash = types::parent_hash(&hash, &next_hash);
                        let next_to_prove = util::parent(pos, total_rows);

                        Proof::sorted_push(&mut nodes, (next_to_prove, hash));

                        // Since we consumed 2 elements from nodes, skip one more here
                        // We need make this explicitly because peek, by definition
                        // does not advance the iterator.
                        row_nodes.next();

                        continue;
                    }
                }

                // If the next node is not my sibling, the hash must be passed inside the proof
                if let Some(next_proof_hash) = hashes_iter.next() {
                    let hash = if util::is_left_niece(pos) {
                        types::parent_hash(&hash, next_proof_hash)
                    } else {
                        types::parent_hash(next_proof_hash, &hash)
                    };

                    let next_to_prove = util::parent(pos, total_rows);

                    Proof::sorted_push(&mut nodes, (next_to_prove, hash));
                } else {
                    return Err(String::from("Proof too short"));
                }
            }
        }

        Ok(calculated_root_hashes)
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
    use core::panic;
    use std::{str::FromStr, vec};

    use bitcoin_hashes::{sha256, Hash, HashEngine};

    use super::Proof;
    use crate::accumulator::stump::Stump;

    fn hash_from_u8(value: u8) -> bitcoin_hashes::sha256::Hash {
        let mut engine = bitcoin_hashes::sha256::Hash::engine();

        engine.input(&[value]);

        sha256::Hash::from_engine(engine)
    }

    fn run_single_case(case: &serde_json::Value) {
        let mut s = Stump::new();

        let mut hashes = Vec::new();

        if let Some(roots) = case["roots"].as_array() {
            for root in roots {
                s.roots
                    .push(bitcoin_hashes::sha256::Hash::from_str(root.as_str().unwrap()).unwrap());
            }
            s.leafs = case["leafs"].as_u64().expect("Missing leafs count");
        } else if let Some(leafs) = case["leaf_values"].as_array() {
            for i in leafs {
                hashes.push(hash_from_u8(i.as_u64().unwrap() as u8));
            }

            s = s
                .modify(&hashes, &vec![], &Proof::default())
                .expect("Test stump is valid");
        } else {
            panic!("Missing test data");
        }

        let json_targets = case["targets"].as_array().expect("Test case misformed");
        let json_proof_hashes = case["proof"].as_array().expect("Test case misformed");
        let json_del_values = case["values"].as_array();

        let mut targets = vec![];
        let mut del_hashes = vec![];
        let mut proof_hashes = vec![];

        for i in json_targets {
            targets.push(i.as_u64().unwrap());
        }

        if let Some(values) = json_del_values {
            for i in values.iter() {
                let value = i.as_u64().unwrap();
                del_hashes.push(hash_from_u8(value as u8));
            }
        } else {
            for i in targets.iter() {
                del_hashes.push(hash_from_u8(*i as u8));
            }
        }

        for i in json_proof_hashes {
            proof_hashes.push(bitcoin_hashes::sha256::Hash::from_str(i.as_str().unwrap()).unwrap());
        }

        let p = Proof::new(targets, proof_hashes);
        let expected = case["expected"].as_bool().unwrap();

        if let Ok(res) = p.verify(&del_hashes, &s) {
            assert!(expected == res);
        }
    }
    #[test]
    fn test_proof_after_deletion() {
        let mut hashes = vec![];
        for i in 0..20 {
            hashes.push(hash_from_u8(i as u8));
        }
        let s = Stump::new()
            .modify(&hashes, &vec![], &Proof::new(vec![], vec![]))
            .expect("Modify should not fail");

        let proof = Proof::new(
            vec![1, 16, 10],
            vec![
                bitcoin_hashes::sha256::Hash::from_str(
                    "6e340b9cffb37a989ca544e6bb780a2c78901d3fb33738768511a30617afa01d",
                )
                .unwrap(),
                bitcoin_hashes::sha256::Hash::from_str(
                    "e7cf46a078fed4fafd0b5e3aff144802b853f8ae459a4f0c14add3314b7cc3a6",
                )
                .unwrap(),
                bitcoin_hashes::sha256::Hash::from_str(
                    "4a64a107f0cb32536e5bce6c98c393db21cca7f4ea187ba8c4dca8b51d4ea80a",
                )
                .unwrap(),
                bitcoin_hashes::sha256::Hash::from_str(
                    "9576f4ade6e9bc3a6458b506ce3e4e890df29cb14cb5d3d887672aef55647a2b",
                )
                .unwrap(),
                bitcoin_hashes::sha256::Hash::from_str(
                    "cd9c77062a338e63a63ca623db438cb8676f15466641079ee61ec2dda98de796",
                )
                .unwrap(),
                bitcoin_hashes::sha256::Hash::from_str(
                    "96d56447466674521007145ed72f8757517c72f7737dc4a0dcd3ecb996968971",
                )
                .unwrap(),
                bitcoin_hashes::sha256::Hash::from_str(
                    "29590a14c1b09384b94a2c0e94bf821ca75b62eacebc47893397ca88e3bbcbd7",
                )
                .unwrap(),
                bitcoin_hashes::sha256::Hash::from_str(
                    "e799acb98a071c4884707e4bc8c093ba22571c8d84cc0223ab0c2c9327313a5b",
                )
                .unwrap(),
            ],
        );
        let proof_after = proof.proof_after_deletion(s.leafs).unwrap();
        let (del_hashes, proof) = proof_after;
        let roots = proof.create_root_candidates(&del_hashes, &s).unwrap();

        // They are swapped, because create_root_candidates builds the forest bottom-up
        let expected = vec![
            bitcoin_hashes::sha256::Hash::from_str(
                "21326d8aebeb6ef7bc02f40bdf778a02ba1c836b257f946ae21cab2a6f95fa18",
            )
            .unwrap(),
            bitcoin_hashes::sha256::Hash::from_str(
                "37968ef73d30dda38ede8357d66593c72acd4f0eb9f7a1a9acfeb7de850c05b4",
            )
            .unwrap(),
        ];
        assert_eq!(expected, roots);
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
