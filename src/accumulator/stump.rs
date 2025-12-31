//! A [Stump] is a basic data structure used in Utreexo. It only holds the roots and the number of leaves
//! in the accumulator. This is useful to create lightweight nodes, the still validates, but is more compact,
//! perfect to clients running on low-power devices.
//!
//! ## Example
//! ```
//! use std::str::FromStr;
//!
//! use rustreexo::accumulator::node_hash::BitcoinNodeHash;
//! use rustreexo::accumulator::proof::Proof;
//! use rustreexo::accumulator::stump::Stump;
//! // Create a new empty Stump
//! let s = Stump::new();
//! // The newly create outputs
//! let utxos = vec![BitcoinNodeHash::from_str(
//!     "b151a956139bb821d4effa34ea95c17560e0135d1e4661fc23cedc3af49dac42",
//! )
//! .unwrap()];
//! // The spent outputs
//! let stxos = vec![];
//! // Modify the Stump, adding the new outputs and removing the spent ones, notice how
//! // it returns a new Stump, instead of modifying the old one. This is due to the fact
//! // that modify is a pure function that doesn't modify the old Stump.
//! let s = s.modify(&utxos, &stxos, &Proof::<BitcoinNodeHash>::default());
//! assert!(s.is_ok());
//! assert_eq!(s.unwrap().roots, utxos);
//! ```

use std::collections::BTreeSet;
use std::io::Read;
use std::io::Write;
use std::vec;

#[cfg(feature = "with-serde")]
use serde::Deserialize;
#[cfg(feature = "with-serde")]
use serde::Serialize;

use super::node_hash::AccumulatorHash;
use super::node_hash::BitcoinNodeHash;
use super::proof::Proof;
use super::util;
use crate::accumulator::proof::RootsOldNew;

#[derive(Debug, Clone, Default)]
pub struct UpdateData<Hash: AccumulatorHash> {
    /// to_destroy is the positions of the empty roots removed after the add.
    pub(crate) to_destroy: Vec<u64>,
    /// pre_num_leaves is the numLeaves of the stump before the add.
    pub(crate) prev_num_leaves: u64,
    /// new_add are the new hashes for the newly created roots after the addition.
    pub(crate) new_add: Vec<(u64, Hash)>,
    /// new_del are the new hashes after the deletion.
    pub(crate) new_del: Vec<(u64, Hash)>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
/// The error kinds returned by Stump's methods
pub enum StumpError {
    /// User passed in a proof that doesn't have any elements, but a non-zero list of
    /// targets.
    EmptyProof,

    /// An IO error occurred, this is usually due to a failure in reading or writing
    /// the Stump to a reader/writer. This error will be returned during (de)serialization.
    Io(std::io::ErrorKind),

    /// The provided proof is invalid. This will happen during proof verification and stump
    /// modification.
    InvalidProof(String),
}

impl From<std::io::Error> for StumpError {
    fn from(err: std::io::Error) -> Self {
        Self::Io(err.kind())
    }
}

#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "with-serde", derive(Serialize, Deserialize))]
pub struct Stump<Hash: AccumulatorHash = BitcoinNodeHash> {
    pub leaves: u64,
    pub roots: Vec<Hash>,
}

impl Default for Stump {
    fn default() -> Self {
        Self::new()
    }
}

impl Stump {
    /// Creates an empty Stump
    ///# Example
    /// ```
    /// use rustreexo::accumulator::stump::Stump;
    /// let s = Stump::new();
    /// ```
    pub fn new() -> Self {
        Self {
            leaves: 0,
            roots: Vec::new(),
        }
    }

    /// Serialize the Stump into a byte array
    /// # Example
    /// ```
    /// use rustreexo::accumulator::node_hash::BitcoinNodeHash;
    /// use rustreexo::accumulator::proof::Proof;
    /// use rustreexo::accumulator::stump::Stump;
    /// let hashes = [0, 1, 2, 3, 4, 5, 6, 7]
    ///     .iter()
    ///     .map(|&el| BitcoinNodeHash::from([el; 32]))
    ///     .collect::<Vec<_>>();
    /// let stump = Stump::new()
    ///     .modify(&hashes, &[], &Proof::default())
    ///     .unwrap();
    /// let mut writer = Vec::new();
    /// stump.serialize(&mut writer).unwrap();
    /// assert_eq!(
    ///     writer,
    ///     vec![
    ///         8, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 150, 124, 244, 241, 98, 69, 217,
    ///         222, 235, 97, 61, 137, 135, 76, 197, 134, 232, 173, 253, 8, 28, 17, 124, 123, 16, 4,
    ///         66, 30, 63, 113, 246, 74,
    ///     ]
    /// );
    /// ```
    pub fn serialize<Dst: Write>(&self, mut writer: &mut Dst) -> Result<u64, StumpError> {
        let mut len = 8;
        writer.write_all(&self.leaves.to_le_bytes())?;
        writer.write_all(&(self.roots.len() as u64).to_le_bytes())?;

        for root in self.roots.iter() {
            len += 32;
            root.write(&mut writer)?;
        }

        Ok(len)
    }

    /// Rewinds old tree state, this should be used in case of reorgs.
    /// Takes the ownership over `old_state`.
    ///# Example
    /// ```
    /// use rustreexo::accumulator::node_hash::BitcoinNodeHash;
    /// use rustreexo::accumulator::proof::Proof;
    /// use rustreexo::accumulator::stump::Stump;
    ///
    /// let s_old = Stump::new();
    /// let mut s_new = Stump::new();
    ///
    /// let s_old = s_old.modify(&vec![], &vec![], &Proof::default()).unwrap();
    /// s_new = s_old.clone();
    /// s_new = s_new.modify(&vec![], &vec![], &Proof::default()).unwrap();
    ///
    /// // A reorg happened
    /// s_new.undo(s_old);
    /// ```
    pub fn undo(&mut self, old_state: Self) {
        self.leaves = old_state.leaves;
        self.roots = old_state.roots;
    }
}

impl<Hash: AccumulatorHash> Stump<Hash> {
    /// Verifies the proof against the Stump. The proof is a list of hashes that are used to
    /// recompute the root of the accumulator. The del_hashes are the hashes that are being
    /// deleted from the accumulator.
    /// // TODO: Add example
    pub fn verify(&self, proof: &Proof<Hash>, del_hashes: &[Hash]) -> Result<bool, StumpError> {
        proof
            .verify(del_hashes, &self.roots, self.leaves)
            .map_err(StumpError::InvalidProof)
    }

    /// Creates a new Stump with a custom hash type
    ///
    /// If you need to use a hash type that's not the [BitcoinNodeHash], you can use this
    /// function to create a new Stump with the desired hash type. Use [BitcoinNodeHash::new]
    /// to create a new Stump with the default hash type.
    pub fn new_with_hash() -> Self {
        Self {
            leaves: 0,
            roots: Vec::new(),
        }
    }

    /// Modify is the external API to change the accumulator state. Since order
    /// matters, you can only modify, providing a list of utxos to be added,
    /// and txos to be removed, along with it's proof. Either may be
    /// empty.
    ///# Example
    /// ```
    /// use std::str::FromStr;
    ///
    /// use rustreexo::accumulator::node_hash::BitcoinNodeHash;
    /// use rustreexo::accumulator::proof::Proof;
    /// use rustreexo::accumulator::stump::Stump;
    ///
    /// let s = Stump::new();
    /// let utxos = vec![BitcoinNodeHash::from_str(
    ///     "b151a956139bb821d4effa34ea95c17560e0135d1e4661fc23cedc3af49dac42",
    /// )
    /// .unwrap()];
    /// let stxos = vec![];
    /// let s = s.modify(&utxos, &stxos, &Proof::default());
    /// assert!(s.is_ok());
    /// assert_eq!(s.unwrap().roots, utxos);
    /// ```
    pub fn modify(
        &self,
        utxos: &[Hash],
        del_hashes: &[Hash],
        proof: &Proof<Hash>,
    ) -> Result<Self, StumpError> {
        let mut computed_roots = self.remove(del_hashes, proof)?;
        let mut new_roots = vec![];

        for root in self.roots.iter() {
            if let Some(pos) = computed_roots.iter().position(|(old, _new)| old == root) {
                let (old_root, new_root) = computed_roots.remove(pos);
                if old_root == *root {
                    new_roots.push(new_root);
                    continue;
                }
            }

            new_roots.push(*root);
        }

        // If there are still roots to be added, it means that the proof is invalid
        // as we should have consumed all the roots.
        if !computed_roots.is_empty() {
            return Err(StumpError::EmptyProof);
        }

        let roots = Self::add(new_roots, utxos, self.leaves);

        let new_stump = Self {
            leaves: self.leaves + utxos.len() as u64,
            roots,
        };

        Ok(new_stump)
    }

    pub fn get_update_data(
        &self,
        utxos: &[Hash],
        del_hashes: &[Hash],
        proof: &Proof<Hash>,
    ) -> Result<UpdateData<Hash>, StumpError> {
        let zeroed_del_hashes = del_hashes.iter().map(|_| Hash::empty()).collect::<Vec<_>>();
        let (intermediate, _) = proof
            .calculate_hashes(&zeroed_del_hashes, self.leaves)
            .map_err(StumpError::InvalidProof)?;
        let mut computed_roots = self.remove(del_hashes, proof)?;
        let mut new_roots = vec![];

        for root in self.roots.iter() {
            if let Some(pos) = computed_roots.iter().position(|(old, _new)| old == root) {
                let (old_root, new_root) = computed_roots.remove(pos);
                if old_root == *root {
                    new_roots.push(new_root);
                    continue;
                }
            }

            new_roots.push(*root);
        }
        let (_, updated, destroyed) = Self::compute_update_data_add(new_roots, utxos, self.leaves);

        let update_data = UpdateData {
            new_add: updated,
            prev_num_leaves: self.leaves,
            to_destroy: destroyed,
            new_del: intermediate,
        };

        Ok(update_data)
    }

    /// Deserialize the Stump from a Reader
    /// # Example
    /// ```
    /// use rustreexo::accumulator::node_hash::BitcoinNodeHash;
    /// use rustreexo::accumulator::proof::Proof;
    /// use rustreexo::accumulator::stump::Stump;
    /// let buffer = vec![
    ///     8, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 150, 124, 244, 241, 98, 69, 217, 222,
    ///     235, 97, 61, 137, 135, 76, 197, 134, 232, 173, 253, 8, 28, 17, 124, 123, 16, 4, 66, 30, 63,
    ///     113, 246, 74,
    /// ];
    /// let mut buffer = std::io::Cursor::new(buffer);
    /// let hashes = [0, 1, 2, 3, 4, 5, 6, 7]
    ///     .iter()
    ///     .map(|&el| BitcoinNodeHash::from([el; 32]))
    ///     .collect::<Vec<_>>();
    /// let stump = Stump::new()
    ///     .modify(&hashes, &[], &Proof::default())
    ///     .unwrap();
    /// assert_eq!(
    ///     stump,
    ///     Stump::<BitcoinNodeHash>::deserialize(buffer).unwrap()
    /// );
    /// ```
    pub fn deserialize<Source: Read>(mut data: Source) -> Result<Self, StumpError> {
        let leaves = util::read_u64(&mut data)?;
        let roots_len = util::read_u64(&mut data)?;
        let mut roots = vec![];

        for _ in 0..roots_len {
            let root = Hash::read(&mut data)?;
            roots.push(root);
        }

        Ok(Self { leaves, roots })
    }

    fn remove(
        &self,
        del_hashes: &[Hash],
        proof: &Proof<Hash>,
    ) -> Result<RootsOldNew<Hash>, StumpError> {
        if del_hashes.is_empty() {
            return Ok(self.roots.iter().map(|root| (*root, *root)).collect());
        }

        let del_hashes = del_hashes
            .iter()
            .map(|hash| (*hash, Hash::empty()))
            .collect::<Vec<_>>();

        proof
            .calculate_hashes_delete(&del_hashes, self.leaves)
            .map_err(StumpError::InvalidProof)
    }

    fn add(mut roots: Vec<Hash>, utxos: &[Hash], mut leaves: u64) -> Vec<Hash> {
        for add in utxos.iter() {
            let pos = leaves;
            let mut h = 0;
            let mut to_add = *add;
            while (pos >> h) & 1 == 1 {
                let root = roots.pop().unwrap();

                to_add = match (root.is_empty(), to_add.is_empty()) {
                    (true, true) => Hash::empty(),
                    (true, false) => to_add,
                    (false, true) => root,
                    (false, false) => AccumulatorHash::parent_hash(&root, &to_add),
                };

                h += 1;
            }
            roots.push(to_add);
            leaves += 1;
        }

        roots
    }

    /// Adds new leaves into the root
    fn compute_update_data_add(
        mut roots: Vec<Hash>,
        utxos: &[Hash],
        mut leaves: u64,
    ) -> (Vec<Hash>, Vec<(u64, Hash)>, Vec<u64>) {
        let after_rows = util::tree_rows(leaves + (utxos.len() as u64));
        let mut updated_subtree: BTreeSet<(u64, Hash)> = BTreeSet::new();
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
                        updated_subtree.insert((util::left_sibling(pos), root));
                        updated_subtree.insert((pos, to_add));
                        pos = util::parent(pos, after_rows);

                        to_add = AccumulatorHash::parent_hash(&root, &to_add);
                    }
                }
                h += 1;
            }

            updated_subtree.insert((pos, to_add));

            roots.push(to_add);
            leaves += 1;
        }
        (roots, updated_subtree.into_iter().collect(), all_deleted)
    }
}

#[cfg(test)]
mod test {
    use std::fmt::Display;
    use std::io::Read;
    use std::io::Write;
    use std::str::FromStr;
    use std::vec;

    use serde::Deserialize;

    use super::Stump;
    use crate::accumulator::node_hash::AccumulatorHash;
    use crate::accumulator::node_hash::BitcoinNodeHash;
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
    fn test_custom_hash_type() {
        #[derive(Debug, Default, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
        struct CustomHash([u8; 32]);

        impl Display for CustomHash {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{:?}", self.0)
            }
        }

        impl AccumulatorHash for CustomHash {
            fn empty() -> Self {
                Self([0; 32])
            }
            fn is_empty(&self) -> bool {
                self.0.iter().all(|&x| x == 0)
            }
            fn parent_hash(left: &Self, right: &Self) -> Self {
                let mut hash = [0; 32];
                #[allow(clippy::needless_range_loop)]
                for i in 0..32 {
                    hash[i] = left.0[i] ^ right.0[i];
                }
                Self(hash)
            }
            fn read<R: Read>(reader: &mut R) -> std::io::Result<Self> {
                let mut hash = [0; 32];
                reader
                    .read_exact(&mut hash)
                    .map_err(|e| e.to_string())
                    .unwrap();
                Ok(Self(hash))
            }
            fn write<W: Write>(&self, writer: &mut W) -> std::io::Result<()> {
                writer
                    .write_all(&self.0)
                    .map_err(|e| e.to_string())
                    .unwrap();
                Ok(())
            }
            fn is_placeholder(&self) -> bool {
                false
            }
            fn placeholder() -> Self {
                Self([0; 32])
            }
        }

        let s = Stump::<CustomHash>::new_with_hash();
        assert!(s.leaves == 0);
        assert!(s.roots.is_empty());

        let hashes = [0, 1, 2, 3, 4, 5, 6, 7]
            .iter()
            .map(|&el| CustomHash([el; 32]))
            .collect::<Vec<_>>();

        let stump = s
            .modify(
                &hashes,
                &[],
                &Proof::<CustomHash>::new_with_hash(Vec::new(), Vec::new()),
            )
            .unwrap();
        assert_eq!(stump.leaves, 8);
        assert_eq!(stump.roots.len(), 1);
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
                .map(|hash| BitcoinNodeHash::from_str(hash).unwrap())
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
                .map(|hash| BitcoinNodeHash::from_str(hash).unwrap())
                .collect::<Vec<_>>();
            let proof_hashes = data
                .proof_hashes
                .iter()
                .map(|hash| BitcoinNodeHash::from_str(hash).unwrap())
                .collect::<Vec<_>>();
            let proof = Proof::new(data.proof_targets, proof_hashes);
            let updated = stump
                .get_update_data(&utxos, &del_hashes, &proof)
                .expect("Update data should be computed correctly");
            // Positions returned after addition
            let new_add_hash: Vec<_> = data
                .new_add_hash
                .iter()
                .map(|hash| BitcoinNodeHash::from_str(hash).unwrap())
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
                .map(|hash| BitcoinNodeHash::from_str(hash).unwrap())
                .collect();
            let new_del: Vec<_> = data
                .new_del_pos
                .into_iter()
                .zip(new_del_hash.into_iter())
                .collect();

            assert_eq!(updated.prev_num_leaves, data.leaves);
            assert_eq!(updated.to_destroy, data.to_destroy);
            assert_eq!(updated.new_add, new_add);
            for del in new_del.iter() {
                assert!(updated.new_del.contains(del));
            }
        }
    }

    #[test]
    fn test_update_data_add() {
        let preimages = vec![0, 1, 2, 3];
        let hashes = preimages.into_iter().map(hash_from_u8).collect::<Vec<_>>();

        let updated = Stump::new()
            .get_update_data(&hashes, &[], &Proof::default())
            .unwrap();

        let positions = vec![0, 1, 2, 3, 4, 5, 6];

        let hashes: Vec<_> = [
            "6e340b9cffb37a989ca544e6bb780a2c78901d3fb33738768511a30617afa01d",
            "4bf5122f344554c53bde2ebb8cd2b7e3d1600ad631c385a5d7cce23c7785459a",
            "dbc1b4c900ffe48d575b5da5c638040125f65db0fe3e24494b76ea986457d986",
            "084fed08b978af4d7d196a7446a86b58009e636b611db16211b65a9aadff29c5",
            "02242b37d8e851f1e86f46790298c7097df06893d6226b7c1453c213e91717de",
            "9576f4ade6e9bc3a6458b506ce3e4e890df29cb14cb5d3d887672aef55647a2b",
            "df46b17be5f66f0750a4b3efa26d4679db170a72d41eb56c3e4ff75a58c65386",
        ]
        .iter()
        .map(|hash| BitcoinNodeHash::from_str(hash).unwrap())
        .collect();

        let positions: Vec<_> = positions.into_iter().zip(hashes).collect();

        assert_eq!(positions, updated.new_add);
    }

    #[test]
    #[cfg(feature = "with-serde")]
    fn test_serde_rtt() {
        let stump = Stump::new()
            .modify(&[hash_from_u8(0), hash_from_u8(1)], &[], &Proof::default())
            .unwrap();
        let serialized = serde_json::to_string(&stump).expect("Serialization failed");
        let deserialized: Stump =
            serde_json::from_str(&serialized).expect("Deserialization failed");
        assert_eq!(stump, deserialized);
    }

    fn run_case_with_deletion(case: TestCase) {
        // If you happen to know whether a leaf will be deleted in the future, you can
        // pretend you've added it, but already account for its deletion. This way, you
        // won't have to call modify twice (once for addition, once for deletion), but
        // the final accumulator will be the same.
        //
        // This is useful for swift sync style clients, where you have a bitmap telling
        // whether a txout is unspent or not. Using this, you don't need to download
        // block proofs and perform fewer hashing, due to not calling `delete` at all.
        let leaf_hashes_without_deletions = case
            .leaf_preimages
            .iter()
            .map(|preimage| {
                let targets = case.target_values.as_ref().unwrap();
                if targets.contains(&(*preimage as u64)) {
                    BitcoinNodeHash::empty()
                } else {
                    hash_from_u8(*preimage)
                }
            })
            .collect::<Vec<_>>();

        let leaf_hashes = case
            .leaf_preimages
            .into_iter()
            .map(hash_from_u8)
            .collect::<Vec<_>>();

        let target_hashes = case
            .target_values
            .as_ref()
            .unwrap()
            .iter()
            .map(|target| hash_from_u8(*target as u8))
            .collect::<Vec<_>>();

        let proof_hashes = case
            .proofhashes
            .unwrap_or_default()
            .into_iter()
            .map(|hash| {
                BitcoinNodeHash::from_str(hash.as_str()).expect("Test case hashes are valid")
            })
            .collect::<Vec<_>>();

        let proof = Proof::new(case.target_values.unwrap(), proof_hashes);

        let roots = case
            .expected_roots
            .into_iter()
            .map(|hash| {
                BitcoinNodeHash::from_str(hash.as_str()).expect("Test case hashes are valid")
            })
            .collect::<Vec<BitcoinNodeHash>>();

        let stump = Stump::new()
            .modify(&leaf_hashes, &[], &Proof::default())
            .expect("This stump is valid");
        let stump = stump.modify(&[], &target_hashes, &proof).unwrap();
        let stump_no_deletion = Stump::new()
            .modify(&leaf_hashes_without_deletions, &[], &Proof::default())
            .expect("This stump is valid");

        assert_eq!(stump.roots, roots);
        assert_eq!(stump.roots, stump_no_deletion.roots);
    }

    fn run_single_addition_case(case: TestCase) {
        let s = Stump::new();
        let test_values = case.leaf_preimages;
        let roots = case.expected_roots;

        let hashes = test_values
            .iter()
            .map(|value| hash_from_u8(*value))
            .collect::<Vec<_>>();

        let s = s
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
            .expect("Stump from test cases are valid");

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
            .map(|&el| BitcoinNodeHash::from([el; 32]))
            .collect::<Vec<_>>();
        let stump = Stump::new()
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

    #[test]
    fn test_update_no_deletion() {
        let leaf_preimages = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11];
        let target_values = [0, 4, 5, 6, 7, 8];
        let leaves = leaf_preimages
            .iter()
            .map(|preimage| {
                if target_values.contains(preimage) {
                    BitcoinNodeHash::empty()
                } else {
                    hash_from_u8(*preimage)
                }
            })
            .collect::<Vec<_>>();

        let acc = Stump::new()
            .modify(&leaves, &[], &Proof::default())
            .unwrap();

        let expected_roots = [
            "2b77298feac78ab51bc5079099a074c6d789bd350442f5079fcba2b3402694e5",
            "84915b5adf9243dd83d67bb7d25b7a0c595ea1c37b97412e21e480c1a46f93bf",
        ]
        .iter()
        .map(|&hash| BitcoinNodeHash::from_str(hash).unwrap())
        .collect::<Vec<_>>();

        assert_eq!(acc.roots, expected_roots);
    }
}

#[cfg(bench)]
mod bench {
    extern crate test;
    use std::convert::TryFrom;

    use test::Bencher;

    use super::Stump;
    use crate::accumulator::node_hash::AccumulatorHash;
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
        .map(|&hash| AccumulatorHash::try_from(hash).unwrap())
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
        .map(|&value| AccumulatorHash::try_from(value).unwrap())
        .collect::<Vec<_>>();
        let acc = Stump::new()
            .modify(&leaves, &vec![], &Proof::default())
            .unwrap();
        let proof = Proof::new(target_values.to_vec(), proofhashes);
        bencher.iter(move || acc.modify(&leaves, &target_hashes, &proof));
    }
}
