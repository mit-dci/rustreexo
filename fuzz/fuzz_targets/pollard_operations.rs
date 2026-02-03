#![no_main]

mod util;

use util::*;

use libfuzzer_sys::fuzz_target;
use rustreexo::accumulator::node_hash::BitcoinNodeHash;
use rustreexo::accumulator::pollard::Pollard;
use rustreexo::accumulator::proof::Proof;

fuzz_target!(|data: FuzzInput| {
    let mut pollard = Pollard::<BitcoinNodeHash>::new();

    for block in data.blocks.iter() {
        pollard
            .modify(&block.additions, &block.removals, Proof::default())
            .unwrap();
    }
});
