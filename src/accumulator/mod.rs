//! This module is the core of the library. It contains all the basic data structures to use Utreexo,
//! such as accumulator, and proofs. Even though the algorithms are equal, you may use different
//! data structures to represent the accumulator, each with its own advantages and disadvantages.
//!
//! # [Stump]
//! A Stump is a basic data structure used in Utreexo. It only holds the roots and the number of leaves
//! in the accumulator. This is useful to create lightweight nodes, the still validates, but is more compact,
//! perfect to clients running on low-power devices.
//!
//! ## Example
//! ```
//!   use rustreexo::accumulator::{types::NodeHash, stump::Stump, proof::Proof};
//!   use std::str::FromStr;
//!   // Create a new empty Stump
//!   let s = Stump::new();
//!   // The newly create outputs
//!   let utxos = vec![NodeHash::from_str("b151a956139bb821d4effa34ea95c17560e0135d1e4661fc23cedc3af49dac42").unwrap()];
//!   // The spent outputs
//!   let stxos = vec![];
//!   // Modify the Stump, adding the new outputs and removing the spent ones, notice how
//!   // it returns a new Stump, instead of modifying the old one. This is due to the fact
//!   // that modify is a pure function, and none of it's operands are modified in the process.
//!   let s = s.modify(&utxos, &stxos, &Proof::default());
//!   assert!(s.is_ok());
//!   assert_eq!(s.unwrap().0.roots, utxos);
//! ```
//!
//! # Proof
//! A proof is a data structure that proves that a given element is in the accumulator. It is used
//! to validate a transaction. A proof is composed of a list of hashes and a list of integers. The
//! hashes are the siblings of the element in the accumulator. The integers are the position of the
//! element in the accumulator.
//! ## Example
//! ```
//!   use bitcoin_hashes::{sha256, Hash, HashEngine};
//!   use std::str::FromStr;
//!   use rustreexo::accumulator::{types::NodeHash, stump::Stump, proof::Proof};
//!   let s = Stump::new();
//!   // Creates a tree with those values as leafs
//!   let test_values:Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7];
//!   // Targets are nodes witch we intend to prove
//!   let targets = vec![0];
//!
//!   // The hashes of the siblings of the targets, used to prove an element.
//!   let mut proof_hashes = Vec::new();

//!   proof_hashes.push(NodeHash::from_str("4bf5122f344554c53bde2ebb8cd2b7e3d1600ad631c385a5d7cce23c7785459a").unwrap());
//!   proof_hashes.push(NodeHash::from_str("9576f4ade6e9bc3a6458b506ce3e4e890df29cb14cb5d3d887672aef55647a2b").unwrap());
//!   proof_hashes.push(NodeHash::from_str("29590a14c1b09384b94a2c0e94bf821ca75b62eacebc47893397ca88e3bbcbd7").unwrap());
//!
//!   // Hashes of the leafs UTXOs we'll add to the accumulator
//!   let mut hashes = Vec::new();
//!   for i in test_values {
//!       let mut engine = sha256::Hash::engine();
//!       engine.input(&[i]);
//!       hashes.push(sha256::Hash::from_engine(engine).into())
//!   }
//!   // Add the UTXOs to the accumulator
//!   let s = s.modify(&hashes, &vec![], &Proof::default()).unwrap().0;
//!   // Create a proof for the targets
//!   let p = Proof::new(targets, proof_hashes);
//!   // Verify the proof
//!   assert!(p.verify(&vec![hashes[0]] , &s).expect("This proof is valid"));
//! ```
pub mod proof;
pub mod stump;
pub mod types;
pub mod util;
