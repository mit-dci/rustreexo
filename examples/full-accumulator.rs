//! An example of a full accumulator. A full accumulator is an accumulator that holds all the
//! elements in the set. It's meant for full nodes, that need to prove membership of arbitrary
//! elements. Clients that only need to verify membership should use a Stump instead.

use std::str::FromStr;

use rustreexo::accumulator::node_hash::NodeHash;
use rustreexo::accumulator::pollard::Pollard;
use rustreexo::accumulator::proof::Proof;
use rustreexo::accumulator::stump::Stump;

fn main() {
    let elements = vec![
        NodeHash::from_str("b151a956139bb821d4effa34ea95c17560e0135d1e4661fc23cedc3af49dac42")
            .unwrap(),
        NodeHash::from_str("d3bd63d53c5a70050a28612a2f4b2019f40951a653ae70736d93745efb1124fa")
            .unwrap(),
    ];
    // Create a new Pollard, and add the utxos to it
    let mut p = Pollard::new();
    p.modify(&elements, &[]).unwrap();

    // Create a proof that the first utxo is in the Pollard
    let proof = p.prove(&[elements[0]]).unwrap();
    // Verify the proof. Notice how we use the del_hashes returned by `prove` here.
    let s = Stump::new()
        .modify(&elements, &[], &Proof::default())
        .unwrap()
        .0;
    assert_eq!(s.verify(&proof, &[elements[0]]), Ok(true));
    // Now we want to update the Pollard, by removing the first utxo, and adding a new one.
    // This would be in case we received a new block with a transaction spending the first utxo,
    // and creating a new one.
    let new_utxo =
        NodeHash::from_str("cac74661f4944e6e1fed35df40da951c6e151e7b0c8d65c3ee37d6dfd3bc3ef7")
            .unwrap();
    p.modify(&[new_utxo], &[elements[0]]).unwrap();

    // Now we can prove that the new utxo is in the Pollard.
    let _ = p.prove(&[new_utxo]).unwrap();
}
