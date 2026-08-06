//! Deserialization robustness fuzz target.
//!
//! Feeds arbitrary bytes to every public deserializer. None of them may
//! panic, abort on allocation, or overflow the stack; malformed input must
//! produce a clean error. Successful parses must round-trip.
//!
//! Expected early crashes (known Tier 0 findings; triage before long runs):
//!   * `Proof::deserialize`: `Vec::with_capacity` on an attacker-controlled
//!     u64 length => capacity-overflow panic / OOM (src/proof/mod.rs:462-474).
//!   * `Pollard` / `MemForest`: unbounded recursion on nested input =>
//!     stack overflow (src/pollard/mod.rs:261-302, src/mem_forest/mod.rs:132-180).
//!   * `Stump::modify` on a deserialized stump whose roots don't match
//!     `popcount(leaves)` => panic; gated by EXERCISE_STATE below.
#![no_main]

use libfuzzer_sys::fuzz_target;
use rustreexo::mem_forest::MemForest;
use rustreexo::node_hash::BitcoinNodeHash;
use rustreexo::pollard::Pollard;
use rustreexo::proof::Proof;
use rustreexo::stump::Stump;

/// Also exercise the state machine on successfully deserialized stumps.
/// Known to trip on malformed stumps; set to false after triage to keep
/// fuzzing for other bugs.
const EXERCISE_STATE: bool = true;

fn one_leaf() -> BitcoinNodeHash {
    BitcoinNodeHash::from([0x42; 32])
}

fuzz_target!(|data: &[u8]| {
    if let Ok(p) = Proof::<BitcoinNodeHash>::deserialize(data) {
        let mut buf = Vec::new();
        p.serialize(&mut buf)
            .expect("serialize of parsed proof must succeed");
        let p2 = Proof::<BitcoinNodeHash>::deserialize(&buf[..])
            .expect("re-parse of own serialization must succeed");
        assert_eq!(p, p2, "proof round-trip mismatch");
    }

    if let Ok(s) = Stump::<BitcoinNodeHash>::deserialize(data) {
        let mut buf = Vec::new();
        s.serialize(&mut buf)
            .expect("serialize of parsed stump must succeed");
        let s2 = Stump::<BitcoinNodeHash>::deserialize(&buf[..])
            .expect("re-parse of own serialization must succeed");
        assert_eq!(s, s2, "stump round-trip mismatch");

        if EXERCISE_STATE {
            // Malformed stumps must produce errors, never panics.
            let _ = s.modify(&[one_leaf()], &[], &Proof::default());
            let _ = s.modify(&[], &[], &Proof::default());
            let _ = s.verify(&Proof::default(), &[]);
        }
    }

    // Deeply nested / malformed input must be rejected without stack
    // overflow or panics (both parsers are recursive).
    let _ = Pollard::<BitcoinNodeHash>::deserialize(&mut &data[..]);
    let _ = MemForest::<BitcoinNodeHash>::deserialize(&data[..]);
});
