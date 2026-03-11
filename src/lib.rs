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

/// This is the maximum size the forest is ever allowed to have, this caps how big `num_leaves` can
/// be (we use a [`u64`]) and is also used by the [`util::translate`] logic.
///
/// # Calculations
///
/// If you think: "but... is 63 enough space"? Well... assuming there's around 999,000 WUs
/// available on each block (let's account for header and coinbase), a non-segwit transaction's
/// size is:
/// `4 (version) + 1 (vin count) + 41 (input) + 5 (vout for many outputs) + 10N + 4 (locktime)`
///
/// `N` is how many outputs we have (we are considering outputs with amount and a zero-sized
/// script), for 999,000 WUs we can fit:
/// - `55 + 10N <= 999,000`
/// - `N ~= 90k` outputs (a little over)
///
/// Since `2^63 = 9,223,372,036,854,775,808`, if you divide this by 90,000 we get
/// 102,481,911,520,608 blocks. It would take us 3,249,680 years to mine that many blocks.
///
/// For the poor soul in 3,249,682 A.D., who needs to fix this hard-fork, here's what you gotta do:
/// - Change the `leaf_data` type to u128, or q128 if Quantum Bits are the fashionable standard.
/// - Change `MAX_FOREST_ROWS` to 128 or higher in `lib.rs`
/// - Modify [`start_position_at_row`] to avoid overflows.
///
/// That should save you the trouble.
pub(crate) const MAX_FOREST_ROWS: u8 = 63;

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
