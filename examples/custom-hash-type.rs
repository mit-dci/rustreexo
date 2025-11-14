//! All data structures in this library are generic over the hash type used, defaulting to
//! [BitcoinNodeHash](crate::accumulator::node_hash::BitcoinNodeHash), the one used by Bitcoin
//! as defined by the utreexo spec. However, if you need to use a different hash type, you can
//! implement the [NodeHash](crate::accumulator::node_hash::NodeHash) trait for it, and use it
//! with the accumulator data structures.
//!
//! This example shows how to use a custom hash type based on the Poseidon hash function. The
//! [Poseidon Hash](https://eprint.iacr.org/2019/458.pdf) is a hash function that is optmized
//! for zero-knowledge proofs, and is used in projects like ZCash and StarkNet.
//! If you want to work with utreexo proofs in zero-knowledge you may want to use this instead
//! of our usual sha512-256 that we use by default, since that will give you smaller circuits.
//! This example shows how to use both the [MemForest](crate::accumulator::MemForest::MemForest) and
//! proofs with a custom hash type. The code here should be pretty much all you need to do to
//! use your custom hashes, just tweak the implementation of
//! [NodeHash](crate::accumulator::node_hash::NodeHash) for your hash type.

use rustreexo::accumulator::mem_forest::MemForest;
use rustreexo::accumulator::node_hash::AccumulatorHash;

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
/// We need a stateful wrapper around the actual hash, this is because we use those different
/// values inside our accumulator. Here we use an enum to represent the different states, you
/// may want to use a struct with more data, depending on your needs.
enum CustomHash {
    /// This means this holds an actual value
    ///
    /// It usually represents a node in the accumulator that haven't been deleted.
    Hash([u8; 32]),
    /// Placeholder is a value that haven't been deleted, but we don't have the actual value.
    /// The only thing that matters about it is that it's not empty. You can implement this
    /// the way you want, just make sure that [NodeHash::is_placeholder] and [NodeHash::placeholder]
    /// returns sane values (that is, if we call [NodeHash::placeholder] calling [NodeHash::is_placeholder]
    /// on the result should return true).
    Placeholder,

    #[default]
    /// This is an empty value, it represents a node that was deleted from the accumulator.
    ///
    /// Same as the placeholder, you can implement this the way you want, just make sure that
    /// [NodeHash::is_empty] and [NodeHash::empty] returns sane values.
    Empty,
}

// you'll need to implement Display for your hash type, so you can print it.
impl std::fmt::Display for CustomHash {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Hash(h) => write!(f, "Hash({h:?})"),
            Self::Placeholder => write!(f, "Placeholder"),
            Self::Empty => write!(f, "Empty"),
        }
    }
}

// this is the implementation of the NodeHash trait for our custom hash type. And it's the only
// thing you need to do to use your custom hash type with the accumulator data structures.
impl AccumulatorHash for CustomHash {
    // returns a new placeholder type such that is_placeholder returns true
    fn placeholder() -> Self {
        Self::Placeholder
    }

    // returns an empty hash such that is_empty returns true
    fn empty() -> Self {
        Self::Empty
    }

    // returns true if this is a placeholder. This should be true iff this type was created by
    // calling placeholder.
    fn is_placeholder(&self) -> bool {
        matches!(self, Self::Placeholder)
    }

    // returns true if this is an empty hash. This should be true iff this type was created by
    // calling empty.
    fn is_empty(&self) -> bool {
        matches!(self, Self::Empty)
    }

    // used for serialization, writes the hash to the writer
    //
    // if you don't want to use serialization, you can just return an error here.
    fn write<W>(&self, writer: &mut W) -> std::io::Result<()>
    where
        W: std::io::Write,
    {
        match self {
            Self::Hash(h) => writer.write_all(h),
            Self::Placeholder => writer.write_all(&[0u8; 32]),
            Self::Empty => writer.write_all(&[0u8; 32]),
        }
    }

    // used for deserialization, reads the hash from the reader
    //
    // if you don't want to use serialization, you can just return an error here.
    fn read<R>(reader: &mut R) -> std::io::Result<Self>
    where
        R: std::io::Read,
    {
        let mut h = [0u8; 32];
        reader.read_exact(&mut h)?;
        if h.iter().all(|&x| x == 0) {
            Ok(Self::Placeholder)
        } else {
            Ok(Self::Hash(h))
        }
    }

    // the main thing about the hash type, it returns the next node's hash, given it's children.
    // The implementation of this method is highly consensus critical, so everywhere should use the
    // exact same algorithm to calculate the next hash. Rustreexo won't call this method, unless
    // **both** children are not empty.
    fn parent_hash(left: &Self, right: &Self) -> Self {
        match (left, right) {
            (Self::Hash(l), Self::Hash(r)) => {
                let mut h = [0u8; 32];
                for i in 0..32 {
                    h[i] = l[i] ^ r[i];
                }
                Self::Hash(h)
            }
            _ => unreachable!(),
        }
    }
}

fn main() {
    // Create a vector with two utxos that will be added to the MemForest
    let elements = vec![CustomHash::Hash([1; 32]), CustomHash::Hash([2; 32])];

    // Create a new MemForest, and add the utxos to it
    let mut p = MemForest::<CustomHash>::new_with_hash();
    p.modify(&elements, &[]).unwrap();

    // Create a proof that the first utxo is in the MemForest
    let proof = p.prove(&[elements[0]]).unwrap();

    // check that the proof has exactly one target
    assert_eq!(proof.n_targets(), 1);
    // check that the proof is what we expect
    assert!(p.verify(&proof, &[elements[0]]).unwrap());
}
