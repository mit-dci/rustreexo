//! This module is the core of the library. It contains all the basic data structures for Utreexo,
//! such as accumulator and proofs. The different data structures are compatible with each other and
//! you may use different data structures to represent the accumulator. Each with its own advantages
//! and disadvantages, and may be selected based on your use case.
//!
//! If you only need to verify and cache proofs used in your wallet, see [stump::Stump],
//! a lightweight implementation of utreexo that only stores roots. Although the [stump::Stump]
//! only keeps the accumulator's roots, it still trustlessly update this state, not requiring
//! a trusted third party to learn about the current state.
pub mod node_hash;
pub mod pollard;
pub mod proof;
pub mod stump;
pub(super) mod util;
