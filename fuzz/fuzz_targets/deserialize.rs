//! Deserialization robustness fuzz target.
//!
//! Feeds arbitrary bytes to every public deserializer. None of them may
//! panic, abort on allocation, or overflow the stack; malformed input must
//! produce a clean error. Successful parses must round-trip.
//!
#![no_main]

use libfuzzer_sys::fuzz_target;
use rustreexo::mem_forest::MemForest;
use rustreexo::node_hash::BitcoinNodeHash;
use rustreexo::pollard::Pollard;
use rustreexo::proof::Proof;
use rustreexo::stump::Stump;

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

        // Malformed stumps must produce errors, never panics.
        let _ = s.modify(&[one_leaf()], &[], &Proof::default());
        let _ = s.modify(&[], &[], &Proof::default());
        let _ = s.verify(&Proof::default(), &[]);
    }

    // Deeply nested / malformed input must be rejected without stack
    // overflow or panics (both parsers are recursive).
    let _ = Pollard::<BitcoinNodeHash>::deserialize(&mut &data[..]);
    let _ = MemForest::<BitcoinNodeHash>::deserialize(&data[..]);
});
