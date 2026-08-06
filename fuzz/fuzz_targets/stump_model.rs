//! Differential state-machine fuzz target.
//!
//! Drives a `Stump` (the compact, verify-only accumulator used by Floresta)
//! and a `MemForest` (the full in-memory forest, used here as the proof
//! oracle) through the same random sequence of additions and deletions, and
//! asserts:
//!
//!   1. No public API ever panics (overflow-checks are enabled in fuzz
//!      builds, so wrapping arithmetic in position math is caught too).
//!   2. After every operation both accumulators commit to the same set of
//!      non-empty roots (ordering is an internal convention, so the
//!      comparison is done sorted).
//!   3. Every proof the oracle generates for live leaves is accepted by the
//!      `Stump`, both via `verify` and via `modify`.
//!   4. `Stump` survives a serialize/deserialize round-trip unchanged.
//!
//! Any assert failure is security-relevant: (2) means state divergence
//! between implementations, (3) means honest proofs are rejected
//! (liveness/DoS for Floresta, which bans the proof peer on failure).
#![no_main]

use libfuzzer_sys::arbitrary::Arbitrary;
use libfuzzer_sys::fuzz_target;
use rustreexo::mem_forest::MemForest;
use rustreexo::node_hash::AccumulatorHash;
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
enum Op {
    /// Append 1..=8 fresh leaves in one `modify`.
    Add { n: u8 },
    /// Delete 1..=4 distinct live leaves using a valid oracle proof.
    Del { idx: [u8; 4], n: u8 },
    /// Prove and verify one random live leaf.
    VerifyOne { idx: u8 },
    /// Serialize/deserialize round-trip of the Stump.
    SerDe,
}

#[derive(Debug, Arbitrary)]
struct Input {
    ops: Vec<Op>,
}

/// The accumulator's commitment, normalized: non-empty roots, sorted.
fn commitment(stump: &Stump, forest: &MemForest) -> (Vec<BitcoinNodeHash>, Vec<BitcoinNodeHash>) {
    let mut a: Vec<_> = stump
        .roots
        .iter()
        .copied()
        .filter(|r| !r.is_empty())
        .collect();
    let mut b: Vec<_> = forest
        .get_roots()
        .iter()
        .map(|r| r.get_data())
        .filter(|r| !r.is_empty())
        .collect();
    a.sort();
    b.sort();
    (a, b)
}

fuzz_target!(|input: Input| {
    let mut stump = Stump::new();
    let mut forest = MemForest::new();
    let mut live: Vec<BitcoinNodeHash> = Vec::new();
    let mut counter: u64 = 0;

    for op in input.ops.iter().take(48) {
        match *op {
            Op::Add { n } => {
                if live.len() > 96 {
                    continue;
                }
                let k = (n % 8) as usize + 1;
                let adds: Vec<_> = (0..k)
                    .map(|_| {
                        let h = leaf(counter);
                        counter += 1;
                        h
                    })
                    .collect();
                stump = stump
                    .modify(&adds, &[], &Proof::default())
                    .expect("add-only modify must succeed")
                    .0;
                forest.modify(&adds, &[]).expect("oracle add must succeed");
                live.extend_from_slice(&adds);
            }
            Op::Del { idx, n } => {
                if live.is_empty() {
                    continue;
                }
                let want = (n % 4) as usize + 1;
                let mut picked: Vec<BitcoinNodeHash> = Vec::new();
                for i in 0..want.min(live.len()) {
                    let h = live[idx[i] as usize % live.len()];
                    if !picked.contains(&h) {
                        picked.push(h);
                    }
                }
                if picked.is_empty() {
                    continue;
                }
                let proof = forest
                    .prove(&picked)
                    .expect("oracle must prove live leaves");
                assert_eq!(
                    stump.verify(&proof, &picked),
                    Ok(true),
                    "LIVENESS: valid batch proof rejected by Stump"
                );
                stump = stump
                    .modify(&[], &picked, &proof)
                    .expect("valid deletion must succeed")
                    .0;
                forest.modify(&[], &picked).expect("oracle delete must succeed");
                live.retain(|h| !picked.contains(h));
            }
            Op::VerifyOne { idx } => {
                if live.is_empty() {
                    continue;
                }
                let h = live[idx as usize % live.len()];
                let proof = forest.prove(&[h]).expect("oracle must prove live leaf");
                assert_eq!(
                    stump.verify(&proof, &[h]),
                    Ok(true),
                    "LIVENESS: valid proof rejected by Stump"
                );
            }
            Op::SerDe => {
                let mut buf = Vec::new();
                stump.serialize(&mut buf).expect("serialize must succeed");
                let back = Stump::deserialize(&buf[..]).expect("deserialize must succeed");
                assert_eq!(stump, back, "stump serialization round-trip mismatch");
            }
        }

        let (a, b) = commitment(&stump, &forest);
        assert_eq!(a, b, "DIVERGENCE: stump/oracle root mismatch after {op:?}");
        assert_eq!(stump.leaves, counter, "leaf count mismatch");
    }
});
