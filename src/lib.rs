//! # Rustreexo
//!
//! Rustreexo is a Rust implementation of [Utreexo](https://eprint.iacr.org/2019/611.pdf),
//! a novel accumulator that allows for a succinct representation of the UTXO set, using a
//! logarithmic amount of space. It uses a dynamic accumulator that allows for addition and deletion
//! of elements. When spending a UTXO, the element is deleted from the accumulator. When receiving a
//! UTXO, the element is added to the accumulator. During validation, nodes receive an inclusion proof
//! for the input in the UTXO set.
//!
//! This library has all building blocks to use Utreexo in a project. It is possible to create
//! an accumulator, add and delete elements to it, verify an elements inclusion in the accumulator,
//! and serialize and deserialize elements.
//!
//! For more information, check each module's documentation.

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

pub mod accumulator;
