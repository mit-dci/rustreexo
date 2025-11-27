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
pub mod accumulator;
