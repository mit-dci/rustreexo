//! A proof is a data structure that proves that a given element is in the accumulator. It is used
//! to validate a transaction. A proof is composed of a list of hashes and a list of integers. The
//! hashes are the hashes need to calculate the root hash for validation. The integers are the position of the
//! element in the accumulator.
//! ## Example
//! ```
//! use std::str::FromStr;
//!
//! use bitcoin_hashes::sha256;
//! use bitcoin_hashes::Hash;
//! use bitcoin_hashes::HashEngine;
//! use rustreexo::accumulator::node_hash::NodeHash;
//! use rustreexo::accumulator::proof::Proof;
//! use rustreexo::accumulator::stump::Stump;
//! let s = Stump::new();
//! // Creates a tree with those values as leaves
//! let test_values: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7];
//! // Targets are the nodes we intend to prove
//! let targets = vec![0];
//!
//! // The hashes used to prove an element.
//! let mut proof_hashes = Vec::new();
//!
//! proof_hashes.push(
//!     NodeHash::from_str("4bf5122f344554c53bde2ebb8cd2b7e3d1600ad631c385a5d7cce23c7785459a")
//!         .unwrap(),
//! );
//! proof_hashes.push(
//!     NodeHash::from_str("9576f4ade6e9bc3a6458b506ce3e4e890df29cb14cb5d3d887672aef55647a2b")
//!         .unwrap(),
//! );
//! proof_hashes.push(
//!     NodeHash::from_str("29590a14c1b09384b94a2c0e94bf821ca75b62eacebc47893397ca88e3bbcbd7")
//!         .unwrap(),
//! );
//!
//! // Hashes of the leaves UTXOs we'll add to the accumulator
//! let mut hashes = Vec::new();
//! for i in test_values {
//!     let mut engine = sha256::Hash::engine();
//!     engine.input(&[i]);
//!     hashes.push(sha256::Hash::from_engine(engine).into())
//! }
//! // Add the UTXOs to the accumulator
//! let s = s.modify(&hashes, &vec![], &Proof::default()).unwrap().0;
//! // Create a proof for the targets
//! let p = Proof::new(targets, proof_hashes);
//! // Verify the proof
//! assert!(s.verify(&p, &vec![hashes[0]]).expect("This proof is valid"));
//! ```
use std::collections::HashMap;
use std::io::Read;
use std::io::Write;

#[cfg(feature = "with-serde")]
use serde::Deserialize;
#[cfg(feature = "with-serde")]
use serde::Serialize;

use super::node_hash::NodeHash;
use super::stump::UpdateData;
use super::util::get_proof_positions;
use super::util::read_u64;
use super::util::tree_rows;
use super::util::{self};
#[derive(Clone, Debug, Default, Eq, PartialEq)]
#[cfg_attr(feature = "with-serde", derive(Serialize, Deserialize))]
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
    pub targets: Vec<u64>,

    /// All the nodes in the tree that are needed to hash up to the root of
    /// the tree. Here, the root is 06. If Targets are [00, 01], then Proof
    /// would be \[05\] as you need 04 and 05 to hash to 06. 04 can be calculated
    /// by hashing 00 and 01.
    ///```!
    /// // 06
    /// // |-------\
    /// // 04      05
    /// // |---\   |---\
    /// // 00  01  02  03
    /// ```
    pub hashes: Vec<NodeHash>,
}
/// We often need to return the targets paired with hashes, and the proof position.
/// Even not using full qualifications, it gets long and complex, and clippy doesn't like
/// it. This type alias helps with that.
pub(crate) type EnumeratedTargetsAndHashPosition = (Vec<(u64, NodeHash)>, Vec<NodeHash>);

impl Proof {
    /// Creates a proof from a vector of target and hashes.
    /// `targets` are u64s and indicates the position of the leaves we are
    /// trying to prove.
    /// `hashes` are of type `NodeHash` and are all hashes we need for computing the roots.
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
    /// use bitcoin_hashes::Hash;
    /// use bitcoin_hashes::HashEngine;
    /// use rustreexo::accumulator::node_hash::NodeHash;
    /// use rustreexo::accumulator::proof::Proof;
    /// let targets = vec![0];
    ///
    /// let mut proof_hashes = Vec::new();
    /// let targets = vec![0];
    /// // For proving 0, we need 01, 09 and 13's hashes. 00, 08, 12 and 14 can be calculated
    /// // Fill `proof_hashes` up with all hashes
    /// Proof::new(targets, proof_hashes);
    /// ```
    pub fn new(targets: Vec<u64>, hashes: Vec<NodeHash>) -> Self {
        Proof { targets, hashes }
    }
    /// Public interface for verifying proofs. Returns a result with a bool or an Error
    /// True means the proof is true given the current stump, false means the proof is
    /// not valid given the current stump.
    ///# Examples
    /// ```
    /// use std::str::FromStr;
    ///
    /// use bitcoin_hashes::sha256;
    /// use bitcoin_hashes::Hash;
    /// use bitcoin_hashes::HashEngine;
    /// use rustreexo::accumulator::node_hash::NodeHash;
    /// use rustreexo::accumulator::proof::Proof;
    /// use rustreexo::accumulator::stump::Stump;
    /// let s = Stump::new();
    /// // Creates a tree with those values as leaves
    /// let test_values: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7];
    /// // Targets are the nodes we intend to prove
    /// let targets = vec![0];
    ///
    /// let mut proof_hashes = Vec::new();
    /// // This tree will look like this
    /// // 14
    /// // |-----------------\
    /// // 12                13
    /// // |---------\       |--------\
    /// // 08       09       10       11
    /// // |----\   |----\   |----\   |----\
    /// // 00   01  02   03  04   05  06   07
    /// // For proving 0, we need 01, 09 and 13's hashes. 00, 08, 12 and 14 can be calculated
    /// proof_hashes.push(
    ///     NodeHash::from_str("4bf5122f344554c53bde2ebb8cd2b7e3d1600ad631c385a5d7cce23c7785459a")
    ///         .unwrap(),
    /// );
    /// proof_hashes.push(
    ///     NodeHash::from_str("9576f4ade6e9bc3a6458b506ce3e4e890df29cb14cb5d3d887672aef55647a2b")
    ///         .unwrap(),
    /// );
    /// proof_hashes.push(
    ///     NodeHash::from_str("29590a14c1b09384b94a2c0e94bf821ca75b62eacebc47893397ca88e3bbcbd7")
    ///         .unwrap(),
    /// );
    ///
    /// let mut hashes = Vec::new();
    /// for i in test_values {
    ///     let mut engine = sha256::Hash::engine();
    ///     engine.input(&[i]);
    ///     hashes.push(sha256::Hash::from_engine(engine).into())
    /// }
    /// let s = s.modify(&hashes, &vec![], &Proof::default()).unwrap().0;
    /// let p = Proof::new(targets, proof_hashes);
    /// assert!(s.verify(&p, &[hashes[0]]).expect("This proof is valid"));
    /// ```
    pub fn verify(
        &self,
        del_hashes: &[NodeHash],
        roots: &[NodeHash],
        num_leaves: u64,
    ) -> Result<bool, String> {
        if self.targets.is_empty() {
            return Ok(true);
        }

        let mut calculated_roots: std::iter::Peekable<std::vec::IntoIter<NodeHash>> = self
            .calculate_hashes(del_hashes, num_leaves)?
            .1
            .into_iter()
            .peekable();

        let mut number_matched_roots = 0;

        for root in roots.iter().rev() {
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
    /// Returns the elements needed to prove a subset of targets. For example, a tree with
    /// 8 leaves, if we cache `[0, 2, 6, 7]`, and we need to prove `[2, 7]` only, we have to remove
    /// elements for 0 and 7. The original proof is `[1, 3, 10]`, and we can compute `[8, 9, 11, 12, 13, 14]`.
    /// But for `[2, 7]` we need `[3, 6, 8, 10]`, and compute `[9, 11, 12, 13, 14]`
    ///```!
    /// // 14
    /// // |---------------\
    /// // 12              13
    /// // |------\        |-------\
    /// // 8       9       10      11
    /// // |---\   |---\   |---\   |---\
    /// // 0   1   2   3   4   5   6   7
    /// ```
    pub fn get_proof_subset(
        &self,
        del_hashes: &[NodeHash],
        new_targets: &[u64],
        num_leaves: u64,
    ) -> Result<Proof, String> {
        let forest_rows = tree_rows(num_leaves);
        let old_proof_positions = get_proof_positions(&self.targets, num_leaves, forest_rows);
        let needed_positions = get_proof_positions(new_targets, num_leaves, forest_rows);
        let (intermediate_positions, _) = self.calculate_hashes(del_hashes, num_leaves)?;

        let mut old_proof = old_proof_positions
            .iter()
            .copied()
            .zip(self.hashes.iter().copied())
            .collect::<HashMap<u64, NodeHash>>();

        old_proof.extend(intermediate_positions);

        let mut new_proof = Vec::new();
        let mut missing_positions = Vec::new();
        for pos in needed_positions {
            if old_proof.contains_key(&pos) {
                new_proof.push((pos, *old_proof.get(&pos).unwrap()));
            } else {
                missing_positions.push(pos);
            }
        }
        new_proof.sort();
        let (_, new_proof): (Vec<u64>, Vec<NodeHash>) = new_proof.into_iter().unzip();
        Ok(Proof {
            targets: new_targets.to_vec(),
            hashes: new_proof,
        })
    }

    /// Serializes the proof into a byte array.
    /// The format is (all integers are little endian):
    /// - number of targets (u64)
    /// - targets (u64)
    /// - number of hashes (u64)
    /// - hashes (32 bytes)
    /// # Example
    /// ```
    /// use rustreexo::accumulator::node_hash::NodeHash;
    /// use rustreexo::accumulator::proof::Proof;
    /// use rustreexo::accumulator::stump::Stump;
    ///
    /// let proof = Proof::default();
    /// let mut serialized_proof = vec![];
    /// proof.serialize(&mut serialized_proof).unwrap();
    /// // An empty proof is only 16 bytes of zeros, meaning no targets and no hashes
    /// assert_eq!(
    ///     vec![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ///     serialized_proof
    /// );
    /// ```
    pub fn serialize<W: Write>(&self, mut writer: W) -> std::io::Result<usize> {
        let mut len = 16;
        writer.write_all(&self.targets.len().to_le_bytes())?;
        for target in &self.targets {
            len += 8;
            writer.write_all(&target.to_le_bytes())?;
        }
        writer.write_all(&self.hashes.len().to_le_bytes())?;
        for hash in &self.hashes {
            len += 32;
            writer.write_all(&**hash)?;
        }
        Ok(len)
    }
    /// Deserializes a proof from a byte array.
    /// # Example
    /// ```
    /// use std::io::Cursor;
    ///
    /// use rustreexo::accumulator::node_hash::NodeHash;
    /// use rustreexo::accumulator::proof::Proof;
    /// use rustreexo::accumulator::stump::Stump;
    /// let proof = Cursor::new(vec![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
    /// let deserialized_proof = Proof::deserialize(proof).unwrap();
    /// // An empty proof is only 16 bytes of zeros, meaning no targets and no hashes
    /// assert_eq!(Proof::default(), deserialized_proof);
    /// ```
    pub fn deserialize<Source: Read>(mut buf: Source) -> Result<Self, String> {
        let targets_len = read_u64(&mut buf)? as usize;

        let mut targets = Vec::with_capacity(targets_len);
        for _ in 0..targets_len {
            targets.push(read_u64(&mut buf).map_err(|_| "Failed to parse target")?);
        }
        let hashes_len = read_u64(&mut buf)? as usize;
        let mut hashes = Vec::with_capacity(hashes_len);
        for _ in 0..hashes_len {
            let mut hash = [0u8; 32];
            buf.read_exact(&mut hash)
                .map_err(|_| "Failed to read hash")?;
            hashes.push(hash.into());
        }
        Ok(Proof { targets, hashes })
    }
    /// Returns how many targets this proof has
    pub fn targets(&self) -> usize {
        self.targets.len()
    }

    /// This function computes a set of roots from a proof.
    /// If some target's hashes are null, then it computes the roots after
    /// those targets are deleted. In this context null means [NodeHash::default].
    ///
    /// It's the caller's responsibility to null out the targets if desired by
    /// passing a `NodeHash::empty()` instead of the actual hash.
    pub(crate) fn calculate_hashes(
        &self,
        del_hashes: &[NodeHash],
        num_leaves: u64,
    ) -> Result<EnumeratedTargetsAndHashPosition, String> {
        // Where all the root hashes that we've calculated will go to.
        let total_rows = util::tree_rows(num_leaves);

        // Where all the parent hashes we've calculated in a given row will go to.
        let mut calculated_root_hashes =
            Vec::<NodeHash>::with_capacity(util::num_roots(num_leaves));

        // As we calculate nodes upwards, it accumulates here
        let mut nodes: Vec<_> = self
            .targets
            .iter()
            .copied()
            .zip(del_hashes.to_owned())
            .collect();

        // Nodes must be sorted for finding siblings during hashing
        nodes.sort();

        // An iterator over proof hashes
        let mut hashes_iter = self.hashes.iter();

        for row in 0..=total_rows {
            // An iterator that only contains nodes of the current row
            // We can't use a iterator over nodes, because we also need no mutable borrow it,
            // clippy will suggest to use nodes.iter().cloned, but this will cause row_nodes to
            // immutably borrow nodes.
            #[allow(clippy::unnecessary_to_owned)]
            let mut row_nodes = nodes
                .to_owned()
                .into_iter()
                .filter(|x| util::detect_row(x.0, total_rows) == row)
                .peekable();

            while let Some((pos, hash)) = row_nodes.next() {
                let next_to_prove = util::parent(pos, total_rows);
                // If the current position is a root, we add that to our result and don't go any further
                if util::is_root_position(pos, num_leaves, total_rows) {
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
                        if hash.is_empty() {
                            Proof::sorted_push(&mut nodes, (next_to_prove, *next_hash));
                        } else if next_hash.is_empty() {
                            Proof::sorted_push(&mut nodes, (next_to_prove, hash));
                        } else {
                            let hash = NodeHash::parent_hash(&hash, next_hash);

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
                    if !hash.is_empty() {
                        let hash = if util::is_left_niece(pos) {
                            NodeHash::parent_hash(&hash, next_proof_hash)
                        } else {
                            NodeHash::parent_hash(next_proof_hash, &hash)
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
    /// Uses the data passed in to update a proof, creating a valid proof for a given
    /// set of targets, after an update. This is useful for caching UTXOs. You grab a proof
    /// for it once and then keep updating it every block, yielding an always valid proof
    /// over those UTXOs.
    pub fn update(
        self,
        cached_hashes: Vec<NodeHash>,
        add_hashes: Vec<NodeHash>,
        block_targets: Vec<u64>,
        remembers: Vec<u64>,
        update_data: UpdateData,
    ) -> Result<(Proof, Vec<NodeHash>), String> {
        let (proof_after_deletion, cached_hashes) = self.update_proof_remove(
            block_targets,
            cached_hashes,
            update_data.new_del,
            update_data.prev_num_leaves,
        )?;

        let data_after_addition = proof_after_deletion.update_proof_add(
            add_hashes,
            cached_hashes,
            remembers,
            update_data.new_add,
            update_data.prev_num_leaves,
            update_data.to_destroy,
        )?;

        Ok(data_after_addition)
    }
    fn update_proof_add(
        self,
        adds: Vec<NodeHash>,
        cached_del_hashes: Vec<NodeHash>,
        remembers: Vec<u64>,
        new_nodes: Vec<(u64, NodeHash)>,
        before_num_leaves: u64,
        to_destroy: Vec<u64>,
    ) -> Result<(Proof, Vec<NodeHash>), String> {
        // Combine the hashes with the targets.
        let orig_targets_with_hash: Vec<(u64, NodeHash)> = self
            .targets
            .iter()
            .copied()
            .zip(cached_del_hashes)
            .collect();

        // Attach positions to the proof.
        let proof_pos = get_proof_positions(
            &self.targets,
            before_num_leaves,
            util::tree_rows(before_num_leaves),
        );
        let proof_with_pos = proof_pos.into_iter().zip(self.hashes).collect();

        // Remap the positions if we moved up a after the addition row.
        let targets_after_remap =
            Proof::maybe_remap(before_num_leaves, adds.len() as u64, orig_targets_with_hash);
        let mut final_targets = targets_after_remap;
        let mut new_nodes_iter = new_nodes.iter();
        let mut proof_with_pos =
            Proof::maybe_remap(before_num_leaves, adds.len() as u64, proof_with_pos);

        let num_leaves = before_num_leaves + (adds.len() as u64);
        // Move up positions that need to be moved up due to the empty roots
        // being written over.
        for node in to_destroy {
            final_targets =
                Proof::calc_next_positions(&vec![node], &final_targets, num_leaves, true)?;
            proof_with_pos =
                Proof::calc_next_positions(&vec![node], &proof_with_pos, num_leaves, true)?;
        }

        // remembers is an index telling what newly created UTXO should be cached
        for remember in remembers {
            let remember_target: Option<&NodeHash> = adds.get(remember as usize);
            if let Some(remember_target) = remember_target {
                let node = new_nodes_iter.find(|(_, hash)| *hash == *remember_target);
                if let Some((pos, hash)) = node {
                    final_targets.push((*pos, *hash));
                }
            }
        }

        final_targets.sort();

        let (new_target_pos, target_hashes): (Vec<_>, Vec<_>) =
            final_targets.clone().into_iter().unzip();
        // Grab all the new nodes after this add.
        let mut needed_proof_positions =
            util::get_proof_positions(&new_target_pos, num_leaves, util::tree_rows(num_leaves));
        needed_proof_positions.sort();

        // We'll use all elements from the old proof, as addition only creates new nodes
        // in our proof (except for root destruction). But before using it, we have to
        // compute the new positions, as adding new elements may move existing elements a few
        // rows up.
        let mut new_proof = proof_with_pos;
        // Iterates over the needed positions and grab them from new_nodes
        // All proof elements must come from the old proof or new_nodes. Old proof elements
        // are already in new_proof. Some every missing element must be in new_nodes.
        for pos in needed_proof_positions {
            if let Some((_, hash)) = new_nodes.iter().find(|(node_pos, _)| pos == *node_pos) {
                new_proof.push((pos, *hash));
            } else {
                // This node must be in either new_nodes or in the old proof, otherwise we can't
                // update our proof
                if !new_proof.iter().any(|(proof_pos, _)| *proof_pos == pos) {
                    return Err(format!("Missing position {}", pos));
                }
            }
        }
        new_proof.sort();

        let (_, hashes): (Vec<u64>, Vec<NodeHash>) = new_proof.into_iter().unzip();
        Ok((
            Proof {
                hashes,
                targets: new_target_pos,
            },
            target_hashes,
        ))
    }
    /// maybe_remap remaps the passed in hash and pos if the tree_rows increase after
    /// adding the new nodes.
    fn maybe_remap(
        num_leaves: u64,
        num_adds: u64,
        positions: Vec<(u64, NodeHash)>,
    ) -> Vec<(u64, NodeHash)> {
        let new_forest_rows = util::tree_rows(num_leaves + num_adds);
        let old_forest_rows = util::tree_rows(num_leaves);
        let tree_rows = util::tree_rows(num_leaves);
        let mut new_proofs = vec![];
        if new_forest_rows > old_forest_rows {
            for (pos, hash) in positions.iter() {
                let row = util::detect_row(*pos, tree_rows);

                let old_start_pos = util::start_position_at_row(row, old_forest_rows);
                let new_start_pos = util::start_position_at_row(row, new_forest_rows);

                let offset = pos - old_start_pos;
                let new_pos = offset + new_start_pos;
                new_proofs.push((new_pos, *hash));
            }
            return new_proofs;
        }

        positions
    }

    /// update_proof_remove modifies the cached proof with the deletions that happen in the block proof.
    /// It updates the necessary proof hashes and un-caches the targets that are being deleted.
    fn update_proof_remove(
        self,
        block_targets: Vec<u64>,
        cached_hashes: Vec<NodeHash>,
        updated: Vec<(u64, NodeHash)>,
        num_leaves: u64,
    ) -> Result<(Proof, Vec<NodeHash>), String> {
        let total_rows = util::tree_rows(num_leaves);

        let targets_with_hash: Vec<(u64, NodeHash)> = self
            .targets
            .iter()
            .cloned()
            .zip(cached_hashes)
            .filter(|(pos, _)| !block_targets.contains(pos))
            .collect();

        let (targets, _): (Vec<_>, Vec<_>) = targets_with_hash.iter().cloned().unzip();
        let proof_positions =
            util::get_proof_positions(&self.targets, num_leaves, util::tree_rows(num_leaves));

        let old_proof: Vec<_> = proof_positions.iter().zip(self.hashes.iter()).collect();

        let mut new_proof = vec![];
        // Grab all the positions of the needed proof hashes.
        let needed_pos = util::get_proof_positions(&targets, num_leaves, total_rows);

        let old_proof_iter = old_proof.iter();
        // Loop through old_proofs and only add the needed proof hashes.
        for (pos, hash) in old_proof_iter {
            // Some positions might not be useful anymore, due to deleted targets
            if needed_pos.contains(*pos) {
                // Grab all positions from the old proof, if it changed, then takes the new
                // hash from `updated`
                if let Some((_, updated_hash)) =
                    updated.iter().find(|(updated_pos, _)| *pos == updated_pos)
                {
                    if !updated_hash.is_empty() {
                        new_proof.push((**pos, *updated_hash));
                    }
                } else {
                    // If it didn't change, take the value from the old proof
                    if !hash.is_empty() {
                        new_proof.push((**pos, **hash));
                    }
                }
            }
        }

        let missing_positions = needed_pos
            .into_iter()
            .filter(|pos| !proof_positions.contains(pos) && !block_targets.contains(pos));

        for missing in missing_positions {
            if let Some((_, hash)) = updated
                .iter()
                .find(|(updated_pos, _)| missing == *updated_pos)
            {
                if !hash.is_empty() {
                    new_proof.push((missing, *hash));
                }
            }
        }

        // We need to remap all proof hashes and sort then, otherwise our hash will be wrong.
        // This happens because deletion moves nodes upwards, some of this nodes may be a proof
        // element. If so we move it to its new position. After that the vector is probably unsorted, so we sort it.

        let mut proof_elements: Vec<_> =
            Proof::calc_next_positions(&block_targets, &new_proof, num_leaves, true)?;

        proof_elements.sort();
        // Grab the hashes for the proof
        let (_, hashes): (Vec<u64>, Vec<NodeHash>) = proof_elements.into_iter().unzip();
        // Gets all proof targets, but with their new positions after delete
        let (targets, target_hashes) =
            Proof::calc_next_positions(&block_targets, &targets_with_hash, num_leaves, true)?
                .into_iter()
                .unzip();

        Ok((Proof { hashes, targets }, target_hashes))
    }

    fn calc_next_positions(
        block_targets: &Vec<u64>,
        old_positions: &Vec<(u64, NodeHash)>,
        num_leaves: u64,
        append_roots: bool,
    ) -> Result<Vec<(u64, NodeHash)>, String> {
        let total_rows = util::tree_rows(num_leaves);
        let mut new_positions = vec![];

        let block_targets = util::detwin(block_targets.to_owned(), total_rows);

        for (position, hash) in old_positions {
            if hash.is_empty() {
                continue;
            }
            let mut next_pos = *position;
            for target in block_targets.iter() {
                if util::is_root_position(next_pos, num_leaves, total_rows) {
                    break;
                }
                // If these positions are in different subtrees, continue.
                let (sub_tree, _, _) = util::detect_offset(*target, num_leaves);
                let (sub_tree1, _, _) = util::detect_offset(next_pos, num_leaves);
                if sub_tree != sub_tree1 {
                    continue;
                }

                if util::is_ancestor(util::parent(*target, total_rows), next_pos, total_rows)? {
                    next_pos = util::calc_next_pos(next_pos, *target, total_rows)?;
                }
            }

            if append_roots || !util::is_root_position(next_pos, num_leaves, total_rows) {
                new_positions.push((next_pos, *hash));
            }
        }
        new_positions.sort();
        Ok(new_positions)
    }
    fn sorted_push(nodes: &mut Vec<(u64, NodeHash)>, to_add: (u64, NodeHash)) {
        let pos = nodes
            .binary_search_by(|(pos, _)| pos.cmp(&to_add.0))
            .unwrap_or_else(|x| x);
        nodes.insert(pos, to_add);
    }
}

#[cfg(test)]
mod tests {
    use std::str::FromStr;

    use serde::Deserialize;

    use super::Proof;
    use crate::accumulator::node_hash::NodeHash;
    use crate::accumulator::stump::Stump;
    use crate::accumulator::util::hash_from_u8;
    #[derive(Deserialize)]
    struct TestCase {
        numleaves: usize,
        roots: Vec<String>,
        targets: Vec<u64>,
        target_preimages: Vec<u8>,
        proofhashes: Vec<String>,
        expected: bool,
    }
    /// This test checks whether our update proof works for different scenarios. We start
    /// with a (valid) cached proof, then we receive `blocks`, like we would in normal Bitcoin
    /// but for this test, block is just random data. For each block we update our Stump and
    /// our proof as well, after that, our proof **must** still be valid for the latest Stump.
    ///
    /// Fix-me: Using derive for deserialize, when also using NodeHash leads to an odd
    /// error that can't be easily fixed. Even bumping version doesn't appear to help.
    /// Deriving hashes directly reduces the amount of boilerplate code used, and makes everything
    /// more clearer, hence, it's preferable.
    #[test]
    fn test_update_proof() {
        #[derive(Debug, Deserialize)]
        struct JsonProof {
            targets: Vec<u64>,
            hashes: Vec<String>,
        }
        #[derive(Debug, Deserialize)]
        struct UpdatedData {
            /// The newly created utxo to be added to our accumulator
            adds: Vec<u64>,
            /// The proof for all destroyed utxos
            proof: JsonProof,
            /// The hash of all destroyed utxos
            del_hashes: Vec<String>,
        }
        #[derive(Debug, Deserialize)]
        struct TestData {
            /// Blocks contains new utxos and utxos that are being deleted
            update: UpdatedData,
            /// The proof we have for our wallet's utxos
            cached_proof: JsonProof,
            /// A initial set of roots, may be empty for starting with an empty stump
            initial_roots: Vec<String>,
            /// The number of leaves in the initial Stump
            initial_leaves: u64,
            /// The hash of all wallet's utxo
            cached_hashes: Vec<String>,
            /// The indexes of all the new utxos to cache
            remembers: Vec<u64>,
            /// After we update our stump, which roots we expect?
            expected_roots: Vec<String>,
            /// After we update the proof, the proof's target should be this
            expected_targets: Vec<u64>,
            /// After we update the proof, the cached hashes should be this
            expected_cached_hashes: Vec<String>,
        }
        let contents = std::fs::read_to_string("test_values/cached_proof_tests.json")
            .expect("Something went wrong reading the file");

        let values: Vec<TestData> =
            serde_json::from_str(contents.as_str()).expect("JSON deserialization error");
        for case_values in values {
            let proof_hashes = case_values
                .cached_proof
                .hashes
                .iter()
                .map(|val| NodeHash::from_str(val).unwrap())
                .collect();
            let cached_hashes: Vec<_> = case_values
                .cached_hashes
                .iter()
                .map(|val| NodeHash::from_str(val).unwrap())
                .collect();

            let cached_proof = Proof::new(case_values.cached_proof.targets, proof_hashes);
            let roots = case_values
                .initial_roots
                .into_iter()
                .map(|hash| NodeHash::from_str(&hash).unwrap())
                .collect();

            let stump = Stump {
                leaves: case_values.initial_leaves,
                roots,
            };

            let utxos = case_values
                .update
                .adds
                .iter()
                .map(|preimage| hash_from_u8(*preimage as u8))
                .collect::<Vec<_>>();
            let del_hashes = case_values
                .update
                .del_hashes
                .iter()
                .map(|hash| NodeHash::from_str(hash).unwrap())
                .collect::<Vec<_>>();
            let block_proof_hashes = case_values
                .update
                .proof
                .hashes
                .iter()
                .map(|hash| NodeHash::from_str(hash).unwrap())
                .collect::<Vec<_>>();

            let block_proof =
                Proof::new(case_values.update.proof.targets.clone(), block_proof_hashes);
            let (stump, updated) = stump.modify(&utxos, &del_hashes, &block_proof).unwrap();
            let (cached_proof, cached_hashes) = cached_proof
                .update(
                    cached_hashes.clone(),
                    utxos,
                    case_values.update.proof.targets,
                    case_values.remembers.clone(),
                    updated.clone(),
                )
                .unwrap();

            let res = stump.verify(&cached_proof, &cached_hashes);

            let expected_roots: Vec<_> = case_values
                .expected_roots
                .iter()
                .map(|hash| NodeHash::from_str(hash).unwrap())
                .collect();

            let expected_cached_hashes: Vec<_> = case_values
                .expected_cached_hashes
                .iter()
                .map(|hash| NodeHash::from_str(hash).unwrap())
                .collect();
            assert_eq!(res, Ok(true));
            assert_eq!(cached_proof.targets, case_values.expected_targets);
            assert_eq!(stump.roots, expected_roots);
            assert_eq!(cached_hashes, expected_cached_hashes);
        }
    }
    #[test]
    fn test_calc_next_positions() {
        use super::Proof;

        #[derive(Clone)]
        struct Test {
            name: &'static str,
            block_targets: Vec<u64>,
            old_positions: Vec<(u64, NodeHash)>,
            num_leaves: u64,
            num_adds: u64,
            append_roots: bool,
            expected: Vec<(u64, NodeHash)>,
        }

        let tests = vec![Test {
            name: "One empty root deleted",
            block_targets: vec![26],
            old_positions: vec![
                (
                    1,
                    NodeHash::from_str(
                        "4bf5122f344554c53bde2ebb8cd2b7e3d1600ad631c385a5d7cce23c7785459a",
                    )
                    .unwrap(),
                ),
                (
                    13,
                    NodeHash::from_str(
                        "9d1e0e2d9459d06523ad13e28a4093c2316baafe7aec5b25f30eba2e113599c4",
                    )
                    .unwrap(),
                ),
                (
                    17,
                    NodeHash::from_str(
                        "9576f4ade6e9bc3a6458b506ce3e4e890df29cb14cb5d3d887672aef55647a2b",
                    )
                    .unwrap(),
                ),
                (
                    25,
                    NodeHash::from_str(
                        "29590a14c1b09384b94a2c0e94bf821ca75b62eacebc47893397ca88e3bbcbd7",
                    )
                    .unwrap(),
                ),
            ],
            num_leaves: 14,
            num_adds: 2,
            append_roots: false,
            expected: (vec![
                (
                    1,
                    NodeHash::from_str(
                        "4bf5122f344554c53bde2ebb8cd2b7e3d1600ad631c385a5d7cce23c7785459a",
                    )
                    .unwrap(),
                ),
                (
                    17,
                    NodeHash::from_str(
                        "9576f4ade6e9bc3a6458b506ce3e4e890df29cb14cb5d3d887672aef55647a2b",
                    )
                    .unwrap(),
                ),
                (
                    21,
                    NodeHash::from_str(
                        "9d1e0e2d9459d06523ad13e28a4093c2316baafe7aec5b25f30eba2e113599c4",
                    )
                    .unwrap(),
                ),
                (
                    25,
                    NodeHash::from_str(
                        "29590a14c1b09384b94a2c0e94bf821ca75b62eacebc47893397ca88e3bbcbd7",
                    )
                    .unwrap(),
                ),
            ]),
        }];

        for test in tests {
            let res = Proof::calc_next_positions(
                &test.block_targets,
                &test.old_positions,
                test.num_leaves + test.num_adds,
                test.append_roots,
            )
            .unwrap();

            assert_eq!(res, test.expected, "testcase: \"{}\" fail", test.name);
        }
    }
    #[test]
    fn test_update_proof_delete() {
        let preimages = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];
        let hashes = preimages.into_iter().map(hash_from_u8).collect::<Vec<_>>();
        let (stump, _) = Stump::new()
            .modify(&hashes, &[], &Proof::default())
            .unwrap();

        let proof_hashes = vec![
            "6e340b9cffb37a989ca544e6bb780a2c78901d3fb33738768511a30617afa01d",
            "084fed08b978af4d7d196a7446a86b58009e636b611db16211b65a9aadff29c5",
            "ca358758f6d27e6cf45272937977a748fd88391db679ceda7dc7bf1f005ee879",
            "9eec588c41d87b16b0ee226cb38da3864f9537632321d8be855a73d5616dcc73",
        ];
        let proof_hashes = proof_hashes
            .into_iter()
            .map(|hash| NodeHash::from_str(hash).unwrap())
            .collect();

        let cached_proof_hashes = [
            "67586e98fad27da0b9968bc039a1ef34c939b9b8e523a8bef89d478608c5ecf6",
            "9576f4ade6e9bc3a6458b506ce3e4e890df29cb14cb5d3d887672aef55647a2b",
            "9eec588c41d87b16b0ee226cb38da3864f9537632321d8be855a73d5616dcc73",
        ];
        let cached_proof_hashes = cached_proof_hashes
            .iter()
            .map(|hash| NodeHash::from_str(hash).unwrap())
            .collect();
        let cached_proof = Proof::new(vec![0, 1, 7], cached_proof_hashes);

        let proof = Proof::new(vec![1, 2, 6], proof_hashes);

        let (stump, modified) = stump
            .modify(
                &[],
                &[hash_from_u8(1), hash_from_u8(2), hash_from_u8(6)],
                &proof,
            )
            .unwrap();
        let (new_proof, _) = cached_proof
            .update_proof_remove(
                vec![1, 2, 6],
                vec![hash_from_u8(0), hash_from_u8(1), hash_from_u8(7)],
                modified.new_del,
                10,
            )
            .unwrap();

        let res = stump.verify(&new_proof, &[hash_from_u8(0), hash_from_u8(7)]);
        assert_eq!(res, Ok(true));
    }
    #[test]
    fn test_calculate_hashes() {
        // Tests if the calculated roots and nodes are correct.
        // The values we use to get some hashes
        let preimages = vec![0, 1, 2, 3, 4, 5, 6, 7];
        let hashes = preimages.into_iter().map(hash_from_u8).collect::<Vec<_>>();
        // Create a new stump with 8 leaves and 1 root
        let s = Stump::new()
            .modify(&hashes, &[], &Proof::default())
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
            .map(|hash| NodeHash::from_str(hash).unwrap())
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
            .map(|root| NodeHash::from_str(root).unwrap())
            .collect();

        let mut expected_computed = expected_hashes
            .iter()
            .map(|hash| NodeHash::from_str(hash).unwrap())
            .zip(&expected_pos);

        let calculated = p.calculate_hashes(&del_hashes, s.leaves);

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
    #[test]
    fn test_serialize_rtt() {
        // Tests if the serialized proof can be deserialized again
        let p = Proof::new(vec![0, 2, 4, 6], vec![]);
        let mut serialized = vec![];
        p.serialize(&mut serialized).unwrap();
        let deserialized = Proof::deserialize(&mut serialized.as_slice()).unwrap();
        assert_eq!(p, deserialized);
    }
    #[test]
    fn test_get_proof_subset() {
        // Tests if the calculated roots and nodes are correct.
        // The values we use to get some hashes
        let preimages = vec![0, 1, 2, 3, 4, 5, 6, 7];
        let hashes = preimages.into_iter().map(hash_from_u8).collect::<Vec<_>>();
        // Create a new stump with 8 leaves and 1 root
        let s = Stump::new()
            .modify(&hashes, &[], &Proof::default())
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
            .map(|hash| NodeHash::from_str(hash).unwrap())
            .collect();

        let p = Proof::new(vec![0, 2, 4, 6], proof_hashes);

        let subset = p.get_proof_subset(&del_hashes, &[0], s.leaves).unwrap();

        assert_eq!(s.verify(&subset, &[del_hashes[0]]), Ok(true));
        assert_eq!(s.verify(&subset, &[del_hashes[2]]), Ok(false));
    }
    #[test]
    #[cfg(feature = "with-serde")]
    fn test_serde_rtt() {
        // This proof is invalid, but don't care for this test
        let proof = Proof::new(vec![0, 1], vec![hash_from_u8(0), hash_from_u8(1)]);
        let serialized = serde_json::to_string(&proof).expect("Serialization failed");
        let deserialized: Proof =
            serde_json::from_str(&serialized).expect("Deserialization failed");
        assert_eq!(proof, deserialized);
    }
    fn run_single_case(case: &serde_json::Value) {
        let case = serde_json::from_value::<TestCase>(case.clone()).expect("Invalid test case");
        let roots = case
            .roots
            .into_iter()
            .map(|root| NodeHash::from_str(root.as_str()).expect("Test case hash is valid"))
            .collect();

        let s = Stump {
            leaves: case.numleaves as u64,
            roots,
        };

        let targets = case.targets;
        let del_hashes = case
            .target_preimages
            .into_iter()
            .map(hash_from_u8)
            .collect::<Vec<_>>();

        let proof_hashes = case
            .proofhashes
            .into_iter()
            .map(|hash| NodeHash::from_str(hash.as_str()).expect("Test case hash is valid"))
            .collect();

        let p = Proof::new(targets, proof_hashes);
        let expected = case.expected;

        let res = s.verify(&p, &del_hashes);
        assert!(Ok(expected) == res);
        // Test getting proof subset (only if the original proof is valid)
        if expected {
            let (subset, _) = p.targets.split_at(p.targets() / 2);
            let proof = p.get_proof_subset(&del_hashes, subset, s.leaves).unwrap();
            let set_hashes = subset
                .iter()
                .map(|preimage| hash_from_u8(*preimage as u8))
                .collect::<Vec<NodeHash>>();

            assert_eq!(s.verify(&proof, &set_hashes), Ok(true));
        }
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

#[cfg(bench)]
mod bench {
    extern crate test;
    use test::Bencher;

    use crate::accumulator::proof::Proof;
    use crate::accumulator::stump::Stump;
    use crate::accumulator::util::hash_from_u8;
    #[bench]
    fn bench_calculate_hashes(bencher: &mut Bencher) {
        let preimages = 0..255_u8;
        let utxos = preimages
            .into_iter()
            .map(|preimage| hash_from_u8(preimage))
            .collect::<Vec<_>>();

        let (stump, modified) = Stump::new().modify(&utxos, &[], &Proof::default()).unwrap();
        let proof = Proof::default();
        let (proof, cached_hashes) = proof
            .update(
                vec![],
                utxos.clone(),
                vec![],
                (0..128).into_iter().collect(),
                modified,
            )
            .unwrap();

        bencher.iter(|| proof.calculate_hashes(&cached_hashes, stump.leaves))
    }
    #[bench]
    fn bench_proof_update(bencher: &mut Bencher) {
        let preimages = [0_u8, 1, 2, 3, 4, 5];
        let utxos = preimages
            .iter()
            .map(|&preimage| hash_from_u8(preimage))
            .collect::<Vec<_>>();

        let (_, modified) = Stump::new().modify(&utxos, &[], &Proof::default()).unwrap();
        let proof = Proof::default();
        let (proof, cached_hashes) = proof
            .update(vec![], utxos.clone(), vec![], vec![0, 3, 5], modified)
            .unwrap();
        let preimages = [6, 7, 8, 9, 10, 11, 12, 13, 14];
        let utxos = preimages
            .iter()
            .map(|&preimage| hash_from_u8(preimage))
            .collect::<Vec<_>>();
        let (_, modified) = Stump::new().modify(&utxos, &cached_hashes, &proof).unwrap();

        bencher.iter(move || {
            proof
                .clone()
                .update(
                    cached_hashes.clone(),
                    utxos.clone(),
                    vec![0, 3, 5],
                    vec![1, 2, 3, 4, 5, 6, 7],
                    modified.clone(),
                )
                .unwrap();
        })
    }
}
