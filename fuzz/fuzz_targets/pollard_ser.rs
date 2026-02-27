#![no_main]

use std::io::Cursor;

use libfuzzer_sys::fuzz_target;
use rustreexo::accumulator::{node_hash::BitcoinNodeHash, pollard::Pollard};

fuzz_target!(|data: &[u8]| {
    let mut cursor = Cursor::new(data);
    let Ok(pollard) = Pollard::<BitcoinNodeHash>::deserialize(&mut cursor) else {
        return;
    };

    let mut serialized_pollard = Vec::new();
    pollard.serialize(&mut serialized_pollard).unwrap();

    assert_eq!(data, serialized_pollard.as_slice());
});
