//! Proof-corruption / soundness fuzz target.
//!
//! Builds a valid accumulator state, obtains a VALID deletion proof from the
//! `MemForest` oracle, applies one fuzzed corruption, then feeds the result
//! to `Stump::verify` and `Stump::modify` — the exact entry points Floresta
//! uses for peer-supplied proofs.
//!
//! Properties asserted:
//!   * never panic (overflow-checks enabled; attacker-controlled positions
//!     such as u64::MAX must be rejected, not crash),
//!   * SOUNDNESS: a proof whose deletion hash was replaced by a non-member,
//!     or with a bit-flipped proof hash, must not verify and must not modify
//!     state.
//!
#![no_main]

use libfuzzer_sys::arbitrary::Arbitrary;
use libfuzzer_sys::fuzz_target;
use rustreexo::mem_forest::MemForest;
use rustreexo::node_hash::BitcoinNodeHash;
use rustreexo::proof::Proof;
use rustreexo::stump::Stump;

/// Deterministic, unique, non-sentinel leaf hash for a counter value.
fn leaf(counter: u64) -> BitcoinNodeHash {
    let mut bytes = [0u8; 32];
    bytes[..8].copy_from_slice(&counter.to_le_bytes());
    bytes[8..16].copy_from_slice(&(!counter).to_be_bytes());
    bytes[16] = 0xa5;
    BitcoinNodeHash::from(bytes)
}

#[derive(Debug, Arbitrary)]
/// Corruption operations applied to a proof.
///
/// To exercise our crypto primitives, we corrupt an otherwise valid proof, making it invalid by a
/// small factor. We then make sure that our code will detect and reject such fraudulent proof,
/// without panicking. This enum contains all possible corruptions we use.
enum Corruption {
    /// Bit-flip one proof hash.
    FlipHash { idx: u8, xor: u8 },

    /// Replace one target with an arbitrary position (biased to edge values).
    ReplaceTarget { idx: u8, pos: u64 },

    /// Drop some proof hashes.
    Truncate { keep: u8 },

    /// Duplicate a target.
    DupTarget { idx: u8 },

    /// Replace one deletion hash with a non-member hash.
    BogusDelHash { idx: u8, fresh: u64 },
}

#[derive(Debug, Arbitrary)]
/// An input to our fuzz target.
struct Input {
    /// How many leaves we should add to our fuzzer
    n_leaves: u8,

    /// Whether we should delete from one more tree.
    second_tree: bool,

    /// The corruption we will apply to this input
    corruption: Corruption,
}

fuzz_target!(|input: Input| {
    let n = 2 + (input.n_leaves % 31) as usize; // 2..=32 leaves
    let leaves: Vec<_> = (0..n as u64).map(leaf).collect();

    let stump = Stump::new()
        .modify(&leaves, &[], &Proof::default())
        .expect("setup add");

    let mut forest = MemForest::new();
    forest.modify(&leaves, &[]).expect("oracle setup");

    // One deletion from the first leaf; optionally a second one from the
    // last leaf (usually a different Merkle tree => multi-root proof).
    let mut dels = vec![leaves[0]];
    if input.second_tree && n > 2 {
        dels.push(leaves[n - 1]);
    }

    let proof = forest.prove(&dels).expect("oracle must provide valid proofs");
    assert_eq!(
        stump.verify(&proof, &dels),
        Ok(true),
        "valid proof rejected by Stump"
    );

    let mut corrupted = proof.clone();
    let mut corrupted_dels = dels.clone();

    // Set when the corruption is guaranteed to invalidate the proof.
    let mut expect_invalid = false;

    match input.corruption {
        Corruption::FlipHash { idx, xor } => {
            if corrupted.hashes.is_empty() || xor == 0 {
                return;
            }
            let i = idx as usize % corrupted.hashes.len();
            if let BitcoinNodeHash::Some(mut inner) = corrupted.hashes[i] {
                inner[0] ^= xor;
                corrupted.hashes[i] = BitcoinNodeHash::from(inner);
                expect_invalid = true;
            }
        }
        Corruption::ReplaceTarget { idx, pos } => {
            if corrupted.targets.is_empty() {
                return;
            }

            let biased = match pos % 4 {
                0 => pos,
                1 => u64::MAX,
                2 => stump.leaves.saturating_add(pos % 64), // just past the end
                _ => pos % stump.leaves.max(1),             // in-range, wrong pairing
            };

            let i = idx as usize % corrupted.targets.len();
            corrupted.targets[i] = biased;
        }
        Corruption::Truncate { keep } => {
            let keep = keep as usize % (corrupted.hashes.len() + 1);

            // this won't corrupt anything
            if corrupted.hashes.len() <= keep.into() {
                return;
            }

            corrupted.hashes.truncate(keep);
            expect_invalid = true;
        }
        Corruption::DupTarget { idx } => {
            if corrupted.targets.is_empty() {
                return;
            }
            let t = corrupted.targets[idx as usize % corrupted.targets.len()];
            corrupted.targets.push(t);
            expect_invalid = true;
        }
        Corruption::BogusDelHash { idx, fresh } => {
            let i = idx as usize % corrupted_dels.len();
            corrupted_dels[i] = leaf(1_000_000u64.saturating_add(fresh)); // guaranteed non-member
            expect_invalid = true;
        }
    }

    // These calls must never panic, whatever the corruption was.
    let v = stump.verify(&corrupted, &corrupted_dels);
    let m = stump.modify(&[], &corrupted_dels, &corrupted);

    if expect_invalid {
        assert_ne!(v, Ok(true), "corrupted proof accepted by verify");
        assert!(m.is_err(), "corrupted proof accepted by modify");
    }
});
