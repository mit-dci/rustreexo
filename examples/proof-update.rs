//! Wallets may hold proofs for it's UTXOs, to prove that UTXO at spending time. Since utreexo
//! is a dynamic accumulator, the proof must be updated, to reflect the changes in the accumulator.
//! By design, utreexo proofs updates gets exponentially less frequent, but still are required.
//!
//! This example shows how to update an existing (valid) proof, and how to get a subset of it.
//! That is, if you have a proof for 1000 UTXOs, and you want to prove that only 10 of them are in the
//! accumulator, you can get a proof for those 10 UTXOs alone.
//!
//! Something nice about how the utreexo accumulator works is that even if you don't have a single
//! leaf cached, you can still prove some elements, given a block Proof. CSNs can always prove their
//! own UTXOs if the can access proofs.

use std::str::FromStr;

use rustreexo::accumulator::node_hash::NodeHash;
use rustreexo::accumulator::proof::Proof;
use rustreexo::accumulator::stump::Stump;

fn main() {
    let s = Stump::new();
    // Get the hashes of the UTXOs we want to insert
    let utxos = get_utxo_hashes1();
    // Add the UTXOs to the accumulator. update_data is the data we need to update the proof
    // after the accumulator is updated.
    let (s, update_data) = s.modify(&utxos, &[], &Proof::default()).unwrap();
    // Create an empty proof, we'll update it to hold our UTXOs
    let p = Proof::default();
    // Update the proof with the UTXOs we added to the accumulator. This proof was initially empty,
    // but we can instruct this function to remember some UTXOs, given their positions in the list of
    // UTXOs we added to the accumulator. In this example, we ask it to cache 0 and 1.
    // Cached hashes are the hashes we care about, after this update, it'll be the hashes of 0 and 1.
    // Add hashes are the newly created UTXOs hashes, block targets are the STXOs being spent.
    // update_data is the data we got from the accumulator update, and contains multiple intermediate
    // data we'll need.
    let (p, cached_hashes) = p
        .update(vec![], utxos.clone(), vec![], vec![0, 1], update_data)
        .unwrap();
    // This should be a valid proof over 0 and 1.
    assert_eq!(p.targets(), 2);
    assert_eq!(s.verify(&p, &cached_hashes), Ok(true));

    // Get a subset of the proof, for the first UTXO only
    let p1 = p.get_proof_subset(&cached_hashes, &[0], s.leaves).unwrap();

    assert_eq!(s.verify(&p1, &cached_hashes), Ok(true));

    // Assume we have a block that (beyond coinbase) spends our UTXO `0` and creates 7 new UTXOs
    // We'll remove `0` as it got spent, and add 1..7 to our cache.
    let new_utxos = get_utxo_hashes2();
    // First, update the accumulator
    let (stump, update_data) = s.modify(&new_utxos, &[utxos[0]], &p1).unwrap();
    // and the proof
    let (p2, cached_hashes) = p
        .update(
            cached_hashes,
            new_utxos,
            vec![0],
            vec![1, 2, 3, 4, 5, 6, 7],
            update_data,
        )
        .unwrap();
    // This should be a valid proof over 1..7
    assert_eq!(stump.verify(&p2, &cached_hashes), Ok(true));
}

/// Returns the hashes for UTXOs in the first block in this fictitious example, there's nothing
/// special about them, they are just the first 8 integers hashed as u8s.
fn get_utxo_hashes1() -> Vec<NodeHash> {
    let hashes = [
        "6e340b9cffb37a989ca544e6bb780a2c78901d3fb33738768511a30617afa01d",
        "4bf5122f344554c53bde2ebb8cd2b7e3d1600ad631c385a5d7cce23c7785459a",
        "dbc1b4c900ffe48d575b5da5c638040125f65db0fe3e24494b76ea986457d986",
        "084fed08b978af4d7d196a7446a86b58009e636b611db16211b65a9aadff29c5",
        "e52d9c508c502347344d8c07ad91cbd6068afc75ff6292f062a09ca381c89e71",
        "e77b9a9ae9e30b0dbdb6f510a264ef9de781501d7b6b92ae89eb059c5ab743db",
        "67586e98fad27da0b9968bc039a1ef34c939b9b8e523a8bef89d478608c5ecf6",
        "ca358758f6d27e6cf45272937977a748fd88391db679ceda7dc7bf1f005ee879",
    ];
    hashes
        .iter()
        .map(|h| NodeHash::from_str(h).unwrap())
        .collect()
}
/// Returns the hashes for UTXOs in the second block.
fn get_utxo_hashes2() -> Vec<NodeHash> {
    let utxo_hashes = [
        "bf4aff60ee0f3b2d82b47b94f6eff3018d1a47d1b0bc5dfbf8d3a95a2836bf5b",
        "2e6adf10ab3174629fc388772373848bbe277ffee1f72568e6d06e823b39d2dd",
        "d47daecc777f21d2c9c1ad6b3332a49dbcc48b821dbe2a59ae880f14d73574fe",
        "cf7d22fd19e030e01d6987678a7e1f1560dfb4e4998f5142b996872c67fc4cf8",
    ];
    utxo_hashes
        .iter()
        .map(|h| NodeHash::from_str(h).unwrap())
        .collect()
}
