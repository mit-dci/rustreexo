use std::collections::HashSet;
use std::fmt::Debug;
use std::ops::ControlFlow;

use libfuzzer_sys::arbitrary;
use libfuzzer_sys::arbitrary::Arbitrary;
use libfuzzer_sys::arbitrary::Unstructured;
use rustreexo::accumulator::node_hash::BitcoinNodeHash;
use rustreexo::accumulator::pollard::PollardAddition;

/// A mock block containing additions and removals to an accumulator.
pub struct Block {
    /// Things being added to the accumulator.
    pub additions: Vec<PollardAddition<BitcoinNodeHash>>,

    /// Things being removed from the accumulator.
    ///
    /// These must already be present in the accumulator.
    pub removals: Vec<BitcoinNodeHash>,
}

impl Debug for Block {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Block")
            .field(
                "additions",
                &self
                    .additions
                    .iter()
                    .map(|a| &a.hash)
                    .collect::<Vec<&BitcoinNodeHash>>(),
            )
            .field("removals", &self.removals)
            .finish()
    }
}

#[derive(Debug)]
/// The input for the fuzzer: a sequence of blocks.
pub struct FuzzInput {
    pub blocks: Vec<Block>,
}

/// Build a BitcoinNodeHash from a u64 by placing the u64 in the first 8 bytes and zeroing the
/// rest.
pub fn build_hash(hash: u64) -> BitcoinNodeHash {
    let mut hash_arr = [0u8; 32];
    hash_arr[..8].copy_from_slice(&hash.to_le_bytes());
    BitcoinNodeHash::from(hash_arr)
}

/// Build a mock block with additions and removals.
pub fn build_block(
    u: &mut Unstructured<'_>,
    txos: &mut HashSet<BitcoinNodeHash>,
    utxos: &mut Vec<PollardAddition<BitcoinNodeHash>>,
) -> arbitrary::Result<Block> {
    let additions_count = u.arbitrary_len::<[u8; 32]>()? % 20;
    let mut additions = Vec::with_capacity(additions_count);
    for _ in 0..additions_count {
        let new_hash_element: u64 = u.arbitrary()?;
        let hash = build_hash(new_hash_element as u64);
        if txos.contains(&hash) {
            continue;
        }

        let addition = PollardAddition {
            hash,
            remember: true,
        };
        additions.push(addition.clone());
    }

    let mut removals = Vec::new();
    u.arbitrary_loop(None, None, |u| {
        if utxos.is_empty() {
            return Ok(std::ops::ControlFlow::Break(()));
        }

        let remove_index = u.arbitrary::<usize>()? % utxos.len();
        let removed = utxos.swap_remove(remove_index);
        removals.push(removed.hash);
        Ok(ControlFlow::Continue(()))
    })?;

    Ok(Block {
        additions,
        removals,
    })
}

impl Arbitrary<'_> for FuzzInput {
    fn arbitrary(
        u: &mut Unstructured<'_>,
    ) -> arbitrary::Result<Self> {
        let n_blocks = u.int_in_range(1..=100)?;
        let mut blocks = Vec::with_capacity(n_blocks);
        let mut utxos = Vec::new();
        let mut txos = HashSet::new();

        for _ in 0..n_blocks {
            let block = build_block(u, &mut txos, &mut utxos)?;
            for addition in &block.additions {
                utxos.push(addition.clone());
                txos.insert(addition.hash);
            }
            blocks.push(block);
        }

        Ok(FuzzInput { blocks })
    }
}
