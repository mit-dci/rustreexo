//! # Rustreexo
//!
//! Rustreexo is a Rust implementation of [Utreexo](https://eprint.iacr.org/2019/611),
//! a novel accumulator that allows for a succinct representation of the UTXO set, using a
//! logarithmic amount of space. It uses a dynamic accumulator that allows for addition and deletion
//! of elements. When spending a UTXO, the element is deleted from the accumulator. When receiving a
//! UTXO, the element is added to the accumulator. During validation, nodes receive an inclusion proof
//! for the input in the UTXO set.
//!
//! This library implements all the building blocks needed to work
//! with the Utreexo accumulator, by way of the following modules:
//!
//!  * [`node_hash`]: the internal representation of a [hash](node_hash::BitcoinNodeHash) in the Utreexo accumulator.
//!  * [`proof`]: the inclusion [`Proof`](proof::Proof) of a leaf in the Utreexo forest.
//!  * [`stump`]: the most compact accumulator. It only keeps track of the forest's roots and can only verify inclusion proofs.
//!  * [`pollard`]: a middle ground between the [`Stump`](stump::Stump) and the [`MemForest`](mem_forest::MemForest).
//!    It allows for keeping track of [`Proof`](proof::Proof)s for a subset of leafs by keeping a forest of sparse Merkle trees.
//!    It can both verify and generate inclusion proofs (proof generation is limited to the leafs that the [`Pollard`](pollard::Pollard)
//!    accumulator keeps). This makes it possible for a node to only keeping track of [`Proof`](proof::Proof)s for a
//!    wallet's own UTXOs in an efficient manner, for example.
//!  * [`mem_forest`]: an in-memory forest accumulator. It keeps track of every leaf in the forest. It can both verify and
//!    generate inclusion proofs for any leaf in the forest.

#![cfg_attr(any(bench), feature(test))]
#![cfg_attr(not(feature = "std"), no_std)]

extern crate alloc;

#[cfg(not(feature = "std"))]
/// Re-exports `alloc` basics plus HashMap/HashSet and IO traits.
pub mod prelude {
    pub use alloc::borrow::ToOwned;
    pub use alloc::format;
    pub use alloc::string::String;
    pub use alloc::string::ToString;
    pub use alloc::vec; // brings `vec!` into scope
    pub use alloc::vec::Vec;

    pub use bitcoin_io as io;
    pub use bitcoin_io::Read;
    pub use bitcoin_io::Write;
    pub use hashbrown::HashMap;
    pub use hashbrown::HashSet;
}

#[cfg(feature = "std")]
/// Re-exports `std` basics plus HashMap/HashSet and IO traits.
pub mod prelude {
    extern crate std;
    pub use std::collections::HashMap;
    pub use std::collections::HashSet;
    pub use std::io;
    pub use std::io::Read;
    pub use std::io::Write;
}

pub mod mem_forest;
pub mod node_hash;
pub mod pollard;
pub mod proof;
pub mod stump;
pub(crate) mod util;
