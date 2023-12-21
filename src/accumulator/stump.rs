//! A [Stump] is a basic data structure used in Utreexo. It only holds the roots and the number of leaves
//! in the accumulator. This is useful to create lightweight nodes, the still validates, but is more compact,
//! perfect to clients running on low-power devices.
//!
//! ## Example
//! ```
//! use std::str::FromStr;
//!
//! use rustreexo::accumulator::node_hash::NodeHash;
//! use rustreexo::accumulator::proof::Proof;
//! use rustreexo::accumulator::stump::Stump;
//! // Create a new empty Stump
//! let s = Stump::new();
//! // The newly create outputs
//! let utxos = vec![NodeHash::from_str(
//!     "b151a956139bb821d4effa34ea95c17560e0135d1e4661fc23cedc3af49dac42",
//! )
//! .unwrap()];
//! // The spent outputs
//! let stxos = vec![];
//! // Modify the Stump, adding the new outputs and removing the spent ones, notice how
//! // it returns a new Stump, instead of modifying the old one. This is due to the fact
//! // that modify is a pure function that doesn't modify the old Stump.
//! let s = s.modify(&utxos, &stxos, &Proof::default());
//! assert!(s.is_ok());
//! assert_eq!(s.unwrap().0.roots, utxos);
//! ```

use std::io::Read;
use std::io::Write;
use std::vec;

#[cfg(feature = "with-serde")]
use serde::Deserialize;
#[cfg(feature = "with-serde")]
use serde::Serialize;

use super::node_hash::NodeHash;
use super::proof::EnumeratedTargetsAndHashPosition;
use super::proof::Proof;
use super::util;

#[derive(Debug, Clone, PartialEq, Default)]
#[cfg_attr(feature = "with-serde", derive(Serialize, Deserialize))]
pub struct Stump {
    pub leaves: u64,
    pub roots: Vec<NodeHash>,
}

#[derive(Debug, Clone, Default)]
pub struct UpdateData {
    /// to_destroy is the positions of the empty roots removed after the add.
    pub(crate) to_destroy: Vec<u64>,
    /// pre_num_leaves is the numLeaves of the stump before the add.
    pub(crate) prev_num_leaves: u64,
    /// new_add are the new hashes for the newly created roots after the addition.
    pub(crate) new_add: Vec<(u64, NodeHash)>,
    /// new_del are the new hashes after the deletion.
    pub(crate) new_del: Vec<(u64, NodeHash)>,
}

impl Stump {
    /// Creates an empty Stump
    ///# Example
    /// ```
    /// use rustreexo::accumulator::stump::Stump;
    /// let s = Stump::new();
    /// ```
    pub fn new() -> Self {
        Stump {
            leaves: 0,
            roots: Vec::new(),
        }
    }
    pub fn verify(&self, proof: &Proof, del_hashes: &[NodeHash]) -> Result<bool, String> {
        proof.verify(del_hashes, &self.roots, self.leaves)
    }
    /// Modify is the external API to change the accumulator state. Since order
    /// matters, you can only modify, providing a list of utxos to be added,
    /// and txos to be removed, along with it's proof. Either may be
    /// empty.
    ///# Example
    /// ```
    /// use std::str::FromStr;
    ///
    /// use rustreexo::accumulator::node_hash::NodeHash;
    /// use rustreexo::accumulator::proof::Proof;
    /// use rustreexo::accumulator::stump::Stump;
    ///
    /// let s = Stump::new();
    /// let utxos = vec![NodeHash::from_str(
    ///     "b151a956139bb821d4effa34ea95c17560e0135d1e4661fc23cedc3af49dac42",
    /// )
    /// .unwrap()];
    /// let stxos = vec![];
    /// let s = s.modify(&utxos, &stxos, &Proof::default());
    /// assert!(s.is_ok());
    /// assert_eq!(s.unwrap().0.roots, utxos);
    /// ```
    pub fn modify(
        &self,
        utxos: &[NodeHash],
        del_hashes: &[NodeHash],
        proof: &Proof,
    ) -> Result<(Stump, UpdateData), String> {
        let mut root_candidates = proof
            .calculate_hashes(del_hashes, self.leaves)?
            .1
            .into_iter()
            .rev()
            .peekable();

        let (intermediate, computed_roots) = self.remove(del_hashes, proof)?;
        let mut computed_roots = computed_roots.into_iter().rev();

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
        let (roots, updated, destroyed) = Stump::add(new_roots, utxos, self.leaves);

        let new_stump = Stump {
            leaves: self.leaves + utxos.len() as u64,
            roots,
        };
        let update_data = UpdateData {
            new_add: updated,
            prev_num_leaves: self.leaves,
            to_destroy: destroyed,
            new_del: intermediate,
        };

        Ok((new_stump, update_data))
    }
    /// Serialize the Stump into a byte array
    /// # Example
    /// ```
    /// use rustreexo::accumulator::node_hash::NodeHash;
    /// use rustreexo::accumulator::proof::Proof;
    /// use rustreexo::accumulator::stump::Stump;
    /// let hashes = [0, 1, 2, 3, 4, 5, 6, 7]
    ///     .iter()
    ///     .map(|&el| NodeHash::from([el; 32]))
    ///     .collect::<Vec<_>>();
    /// let (stump, _) = Stump::new()
    ///     .modify(&hashes, &[], &Proof::default())
    ///     .unwrap();
    /// let mut writer = Vec::new();
    /// stump.serialize(&mut writer).unwrap();
    /// assert_eq!(
    ///     writer,
    ///     vec![
    ///         8, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 150, 124, 244, 241, 98, 69, 217, 222,
    ///         235, 97, 61, 137, 135, 76, 197, 134, 232, 173, 253, 8, 28, 17, 124, 123, 16, 4, 66, 30,
    ///         63, 113, 246, 74,
    ///     ]
    /// );
    /// ```
    pub fn serialize<Dst: Write>(&self, writer: &mut Dst) -> std::io::Result<usize> {
        let mut len = 8;
        writer.write_all(&self.leaves.to_le_bytes())?;
        writer.write_all(&self.roots.len().to_le_bytes())?;
        for root in self.roots.iter() {
            len += 32;
            writer.write_all(&**root)?;
        }
        Ok(len)
    }
    /// Deserialize the Stump from a Reader
    /// # Example
    /// ```
    /// use rustreexo::accumulator::node_hash::NodeHash;
    /// use rustreexo::accumulator::proof::Proof;
    /// use rustreexo::accumulator::stump::Stump;
    /// let buffer = vec![
    ///     8, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 150, 124, 244, 241, 98, 69, 217, 222, 235,
    ///     97, 61, 137, 135, 76, 197, 134, 232, 173, 253, 8, 28, 17, 124, 123, 16, 4, 66, 30, 63, 113,
    ///     246, 74,
    /// ];
    /// let mut buffer = std::io::Cursor::new(buffer);
    /// let hashes = [0, 1, 2, 3, 4, 5, 6, 7]
    ///     .iter()
    ///     .map(|&el| NodeHash::from([el; 32]))
    ///     .collect::<Vec<_>>();
    /// let (stump, _) = Stump::new()
    ///     .modify(&hashes, &[], &Proof::default())
    ///     .unwrap();
    /// assert_eq!(stump, Stump::deserialize(buffer).unwrap());
    /// ```
    pub fn deserialize<Source: Read>(data: Source) -> Result<Self, String> {
        let mut data = data;
        let leaves = util::read_u64(&mut data)?;
        let roots_len = util::read_u64(&mut data)?;
        let mut roots = vec![];

        for _ in 0..roots_len {
            let mut root = [0u8; 32];
            data.read_exact(&mut root).map_err(|e| e.to_string())?;

            roots.push(NodeHash::from(root));
        }
        Ok(Stump { leaves, roots })
    }
    /// Rewinds old tree state, this should be used in case of reorgs.
    /// Takes the ownership over `old_state`.
    ///# Example
    /// ```
    /// use rustreexo::accumulator::proof::Proof;
    /// use rustreexo::accumulator::stump::Stump;
    /// let s_old = Stump::new();
    /// let mut s_new = Stump::new();
    ///
    /// let s_old = s_old.modify(&vec![], &vec![], &Proof::default()).unwrap().0;
    /// s_new = s_old.clone();
    /// s_new = s_new.modify(&vec![], &vec![], &Proof::default()).unwrap().0;
    ///
    /// // A reorg happened
    /// s_new.undo(s_old);
    /// ```
    pub fn undo(&mut self, old_state: Stump) {
        self.leaves = old_state.leaves;
        self.roots = old_state.roots;
    }

    fn remove(
        &self,
        del_hashes: &[NodeHash],
        proof: &Proof,
    ) -> Result<EnumeratedTargetsAndHashPosition, String> {
        if del_hashes.is_empty() {
            return Ok((vec![], self.roots.clone()));
        }

        let del_hashes = vec![NodeHash::empty(); proof.targets()];
        proof.calculate_hashes(&del_hashes, self.leaves)
    }
    /// Adds new leaves into the root
    fn add(
        mut roots: Vec<NodeHash>,
        utxos: &[NodeHash],
        mut leaves: u64,
    ) -> (Vec<NodeHash>, Vec<(u64, NodeHash)>, Vec<u64>) {
        let after_rows = util::tree_rows(leaves + (utxos.len() as u64));
        let mut updated_subtree: Vec<(u64, NodeHash)> = vec![];
        let all_deleted = util::roots_to_destroy(utxos.len() as u64, leaves, &roots);

        for (i, add) in utxos.iter().enumerate() {
            let mut pos = leaves;

            // deleted is the empty roots that are being added over. These force
            // the current root to move up.
            let deleted = util::roots_to_destroy((utxos.len() - i) as u64, leaves, &roots);
            for del in deleted {
                if util::is_ancestor(util::parent(del, after_rows), pos, after_rows).unwrap() {
                    pos = util::calc_next_pos(pos, del, after_rows).unwrap();
                }
            }
            let mut h = 0;
            // Iterates over roots, if we find a root that is not empty, we concatenate with
            // the one we are adding and create new root, leaving this position empty. Stops
            // when find an empty root.

            // You can say if a root is empty, by looking a the binary representations of the
            // number of leaves. If the h'th bit is one, then this position is occupied, empty
            // otherwise.
            let mut to_add = *add;
            while (leaves >> h) & 1 == 1 {
                let root = roots.pop();

                if let Some(root) = root {
                    if !root.is_empty() {
                        updated_subtree.push((util::left_sibling(pos), root));
                        updated_subtree.push((pos, to_add));
                        pos = util::parent(pos, after_rows);

                        to_add = NodeHash::parent_hash(&root, &to_add);
                    }
                }
                h += 1;
            }
            updated_subtree.push((pos, to_add));

            updated_subtree.sort();
            updated_subtree.dedup();

            roots.push(to_add);
            leaves += 1;
        }
        (roots, updated_subtree, all_deleted)
    }
}

#[cfg(test)]
mod test {
    use std::str::FromStr;
    use std::vec;

    use serde::Deserialize;

    use super::Stump;
    use crate::accumulator::node_hash::NodeHash;
    use crate::accumulator::proof::Proof;
    use crate::accumulator::util::hash_from_u8;

    #[derive(Debug, Deserialize)]
    struct TestCase {
        leaf_preimages: Vec<u8>,
        target_values: Option<Vec<u64>>,
        expected_roots: Vec<String>,
        proofhashes: Option<Vec<String>>,
    }

    #[test]
    // Make a few simple tests about stump creation
    fn test_stump() {
        let s = Stump::new();
        assert!(s.leaves == 0);
        assert!(s.roots.is_empty());
    }
    #[test]
    fn test_updated_data() {
        /// This test initializes a Stump, with some utxos. Then, we add a couple more utxos
        /// and delete some others to see what we get back for Modified.
        #[derive(Debug, Deserialize)]
        struct TestData {
            roots: Vec<String>,
            leaves: u64,
            /// New data to add
            additional_preimages: Vec<u64>,
            /// The hash of all targets to be deleted
            del_hashes: Vec<String>,
            /// The hashes that are used to recompute a given Merkle path to the root
            proof_hashes: Vec<String>,
            /// Which nodes are being proven, in this case, they'll be deleted
            proof_targets: Vec<u64>,
            /// Here are the expected values:
            /// During addition, we create those nodes
            new_add_pos: Vec<u64>,
            new_add_hash: Vec<String>,
            /// And during deletion, we destroy or update those
            new_del_pos: Vec<u64>,
            new_del_hashes: Vec<String>,
            to_destroy: Vec<u64>,
        }
        let contents = std::fs::read_to_string("test_values/update_data_tests.json")
            .expect("Something went wrong reading the file");

        let tests = serde_json::from_str::<Vec<TestData>>(contents.as_str())
            .expect("JSON deserialization error");

        for data in tests {
            let roots = data
                .roots
                .iter()
                .map(|hash| NodeHash::from_str(hash).unwrap())
                .collect();
            let stump = Stump {
                leaves: data.leaves,
                roots,
            };

            let utxos = data
                .additional_preimages
                .iter()
                .map(|preimage| hash_from_u8(*preimage as u8))
                .collect::<Vec<_>>();
            let del_hashes = data
                .del_hashes
                .iter()
                .map(|hash| NodeHash::from_str(hash).unwrap())
                .collect::<Vec<_>>();
            let proof_hashes = data
                .proof_hashes
                .iter()
                .map(|hash| NodeHash::from_str(hash).unwrap())
                .collect::<Vec<_>>();
            let proof = Proof::new(data.proof_targets, proof_hashes);
            let (_, updated) = stump.modify(&utxos, &del_hashes, &proof).unwrap();
            // Positions returned after addition
            let new_add_hash: Vec<_> = data
                .new_add_hash
                .iter()
                .map(|hash| NodeHash::from_str(hash).unwrap())
                .collect();
            let new_add: Vec<_> = data
                .new_add_pos
                .into_iter()
                .zip(new_add_hash.into_iter())
                .collect();
            // Positions returned after deletion
            let new_del_hash: Vec<_> = data
                .new_del_hashes
                .iter()
                .map(|hash| NodeHash::from_str(hash).unwrap())
                .collect();
            let new_del: Vec<_> = data
                .new_del_pos
                .into_iter()
                .zip(new_del_hash.into_iter())
                .collect();

            assert_eq!(updated.prev_num_leaves, data.leaves);
            assert_eq!(updated.to_destroy, data.to_destroy);
            assert_eq!(updated.new_add, new_add);
            assert_eq!(updated.new_del, new_del);
        }
    }
    #[test]
    fn test_update_data_add() {
        let preimages = vec![0, 1, 2, 3];
        let hashes = preimages.into_iter().map(hash_from_u8).collect::<Vec<_>>();

        let (_, updated) = Stump::new()
            .modify(&hashes, &[], &Proof::default())
            .unwrap();

        let positions = vec![0, 1, 2, 3, 4, 5, 6];

        let hashes: Vec<_> = ["6e340b9cffb37a989ca544e6bb780a2c78901d3fb33738768511a30617afa01d",
            "4bf5122f344554c53bde2ebb8cd2b7e3d1600ad631c385a5d7cce23c7785459a",
            "dbc1b4c900ffe48d575b5da5c638040125f65db0fe3e24494b76ea986457d986",
            "084fed08b978af4d7d196a7446a86b58009e636b611db16211b65a9aadff29c5",
            "02242b37d8e851f1e86f46790298c7097df06893d6226b7c1453c213e91717de",
            "9576f4ade6e9bc3a6458b506ce3e4e890df29cb14cb5d3d887672aef55647a2b",
            "df46b17be5f66f0750a4b3efa26d4679db170a72d41eb56c3e4ff75a58c65386"]
        .iter()
        .map(|hash| NodeHash::from_str(hash).unwrap())
        .collect();

        let positions: Vec<_> = positions.into_iter().zip(hashes).collect();

        assert_eq!(positions, updated.new_add);
    }

    #[test]
    #[cfg(feature = "with-serde")]
    fn test_serde_rtt() {
        let stump = Stump::new()
            .modify(&[hash_from_u8(0), hash_from_u8(1)], &[], &Proof::default())
            .unwrap()
            .0;
        let serialized = serde_json::to_string(&stump).expect("Serialization failed");
        let deserialized: Stump =
            serde_json::from_str(&serialized).expect("Deserialization failed");
        assert_eq!(stump, deserialized);
    }
    fn run_case_with_deletion(case: TestCase) {
        let leaf_hashes = case
            .leaf_preimages
            .into_iter()
            .map(hash_from_u8)
            .collect::<Vec<_>>();

        let target_hashes = case
            .target_values
            .clone()
            .unwrap()
            .into_iter()
            .map(|target| hash_from_u8(target as u8))
            .collect::<Vec<_>>();

        let proof_hashes = case
            .proofhashes
            .unwrap_or_default()
            .into_iter()
            .map(|hash| NodeHash::from_str(hash.as_str()).expect("Test case hashes are valid"))
            .collect::<Vec<_>>();

        let proof = Proof::new(case.target_values.unwrap(), proof_hashes);

        let roots = case
            .expected_roots
            .into_iter()
            .map(|hash| NodeHash::from_str(hash.as_str()).expect("Test case hashes are valid"))
            .collect::<Vec<NodeHash>>();

        let (stump, _) = Stump::new()
            .modify(&leaf_hashes, &[], &Proof::default())
            .expect("This stump is valid");
        let (stump, _) = stump.modify(&[], &target_hashes, &proof).unwrap();

        assert_eq!(stump.roots, roots);
    }

    fn run_single_addition_case(case: TestCase) {
        let s = Stump::new();
        let test_values = case.leaf_preimages;
        let roots = case.expected_roots;

        let hashes = test_values
            .iter()
            .map(|value| hash_from_u8(*value))
            .collect::<Vec<_>>();

        let (s, _) = s
            .modify(&hashes, &[], &Proof::default())
            .expect("Stump from test cases are valid");

        assert_eq!(s.leaves, hashes.len() as u64);

        for (i, root) in roots.into_iter().enumerate() {
            assert_eq!(root, s.roots[i].to_string());
        }
    }
    #[test]
    fn test_undo() {
        let mut hashes = vec![];
        // Add 100 initial UTXOs
        for i in 0..100_u8 {
            hashes.push(hash_from_u8(i));
        }

        let s_old = Stump::new();
        let s_old = s_old
            .modify(&hashes, &[], &Proof::default())
            .expect("Stump from test cases are valid")
            .0;

        let mut s_new = s_old.clone();

        // Add 100 more UTXOS
        for i in 0..100_u8 {
            hashes.push(hash_from_u8(i));
        }

        s_new
            .modify(&hashes, &[], &Proof::default())
            .expect("Stump from test cases are valid");
        let s_old_copy = s_old.clone();

        // A reorg happened, need to roll back state
        s_new.undo(s_old);

        assert!(s_new == s_old_copy);
    }

    #[test]
    fn test_serialize() {
        let hashes = [0, 1, 2, 3, 4, 5, 6, 7]
            .iter()
            .map(|&el| NodeHash::from([el; 32]))
            .collect::<Vec<_>>();
        let (stump, _) = Stump::new()
            .modify(&hashes, &[], &Proof::default())
            .unwrap();
        let mut writer = Vec::new();
        stump.serialize(&mut writer).unwrap();

        let mut reader = std::io::Cursor::new(writer);
        let stump2 = Stump::deserialize(&mut reader).unwrap();
        assert_eq!(stump, stump2);
    }
    #[test]
    fn run_test_cases() {
        #[derive(Deserialize)]
        struct TestsJSON {
            insertion_tests: Vec<TestCase>,
            deletion_tests: Vec<TestCase>,
        }

        let contents = std::fs::read_to_string("test_values/test_cases.json")
            .expect("Something went wrong reading the file");

        let tests = serde_json::from_str::<TestsJSON>(contents.as_str())
            .expect("JSON deserialization error");

        for i in tests.insertion_tests {
            run_single_addition_case(i);
        }
        for i in tests.deletion_tests {
            run_case_with_deletion(i);
        }
    }
}

#[cfg(bench)]
mod bench {
    extern crate test;
    use std::convert::TryFrom;

    use test::Bencher;

    use super::Stump;
    use crate::accumulator::node_hash::NodeHash;
    use crate::accumulator::proof::Proof;
    use crate::accumulator::util::hash_from_u8;

    #[bench]
    fn bench_addition(bencher: &mut Bencher) {
        let hash = [
            "4bf5122f344554c53bde2ebb8cd2b7e3d1600ad631c385a5d7cce23c7785459a",
            "4bf5122f344554c53bde2ebb8cd2b7e3d1600ad631c385a5d7cce23c7785459b",
            "4bf5122f344554c53bde2ebb8cd2b7e3d1600ad631c385a5d7cce23c7785459c",
            "4bf5122f344554c53bde2ebb8cd2b7e3d1600ad631c385a5d7cce23c7785459d",
            "4bf5122f344554c53bde2ebb8cd2b7e3d1600ad631c385a5d7cce23c7785459e",
            "4bf5122f344554c53bde2ebb8cd2b7e3d1600ad631c385a5d7cce23c7785459f",
        ]
        .iter()
        .map(|&hash| NodeHash::try_from(hash).unwrap())
        .collect::<Vec<_>>();
        let proof = &Proof::default();
        bencher.iter(move || {
            let _ = Stump::new().modify(&hash, &[], &proof);
        });
    }
    #[bench]
    fn bench_add_del(bencher: &mut Bencher) {
        let leaf_preimages = [0_u8, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11];
        let leaves = leaf_preimages
            .iter()
            .map(|preimage| hash_from_u8(*preimage))
            .collect::<Vec<_>>();
        let target_values = [0, 4, 5, 6, 7, 8];
        let target_hashes = target_values
            .iter()
            .map(|val| hash_from_u8(*val as u8))
            .collect::<Vec<_>>();
        let proofhashes = [
            "4bf5122f344554c53bde2ebb8cd2b7e3d1600ad631c385a5d7cce23c7785459a",
            "2b4c342f5433ebe591a1da77e013d1b72475562d48578dca8b84bac6651c3cb9",
            "9576f4ade6e9bc3a6458b506ce3e4e890df29cb14cb5d3d887672aef55647a2b",
            "c413035120e8c9b0ca3e40c93d06fe60a0d056866138300bb1f1dd172b4923c3",
        ]
        .iter()
        .map(|&value| NodeHash::try_from(value).unwrap())
        .collect::<Vec<_>>();
        let acc = Stump::new()
            .modify(&leaves, &vec![], &Proof::default())
            .unwrap()
            .0;
        let proof = Proof::new(target_values.to_vec(), proofhashes);
        bencher.iter(move || acc.modify(&leaves, &target_hashes, &proof));
    }
}
