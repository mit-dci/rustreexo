//! # Utreexo
//! [Utreexo](https://eprint.iacr.org/2019/611.pdf) is a novel accumulator that allows for succinct
//! UTXO set representation, using a logarithmic amount of space. It uses a dynamic accumulator
//! that allows for the addition and deletion of elements. When spending  a UTXO, the element
//! is deleted from the accumulator. When receiving a UTXO, the element is added to the accumulator.
//! During validation, nodes receive a proof which proves the inputs in a block or transaction exist
//! in the UTXO set.
//!
//! This lib have all basic building blocks to use Utreexo in a project. It is possible to create a
//! new accumulator, add and delete elements, verify proofs, and serialize and deserialize then.
//! For more information, check the documentation of each module.
pub mod accumulator;
