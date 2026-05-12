# rustreexo

<p>
    <a href="https://crates.io/crates/rustreexo"><img src="https://img.shields.io/crates/v/rustreexo.svg"/></a>
    <a href="https://docs.rs/rustreexo"><img src="https://img.shields.io/badge/docs.rs-rustreexo-green"/></a>
    <a href="https://blog.rust-lang.org/2023/11/16/Rust-1.74.0/"><img src="https://img.shields.io/badge/rustc-1.74.0%2B-coral.svg"/></a>
    <a href="https://github.com/mit-dci/rustreexo/blob/main/LICENSE"><img src="https://img.shields.io/badge/License-MIT%2FApache--2.0-red.svg"/></a>
    <a href="https://github.com/mit-dci/rustreexo/actions/workflows/rust.yml"><img src="https://img.shields.io/github/actions/workflow/status/mit-dci/rustreexo/rust.yml?label=Rust%20CI"></a>
</p>

A Rust implementation of [Utreexo](https://eprint.iacr.org/2019/611), a dynamic hash-based accumulator optimized for the Bitcoin UTXO set.

Utreexo enables constructing a succinct representation of the Bitcoin UTXO in a logarithmic
amount of size, by leveraging Merkle trees. Set membership can be proven and verified
through Merkle inclusion proofs.

This library implements three accumulator primitives:

- [`Stump`](src/stump/mod.rs): keeps the roots of the Merkle forest, using $O(\log{n})$ space

- [`Pollard`](src/pollard/mod.rs): keeps a specific set of leaves of the Merkle forest, using $O(k \cdot \log{n})$ space

- [`MemForest`](src/mem_forest/mod.rs): keeps all leaves of the Merkle forest, using $O(n)$ space,

where $n$ is the number of leaves, and $k$ is the number of cached leaves.

## Usage

```rs
use rustreexo::node_hash::BitcoinNodeHash;
use rustreexo::proof::Proof;
use rustreexo::stump::Stump;

let utxo = BitcoinNodeHash::from_str("b151a956139bb821d4effa34ea95c17560e0135d1e4661fc23cedc3af49dac42").unwrap();

// Create an accumulator
let stump = Stump::new();

// Add the UTXO to the accumulator
let (stump, _) = stump.modify(&vec![utxo], &[], &Proof::default()).unwrap();

// Create an inclusion proof for the UTXO that was added
let proof = Proof::new(vec![0], vec![utxo]);

// Remove the UTXO from the accumulator by proving its set membership
let (stump, _) = stump.modify(&vec![], &vec![utxo], &proof).unwrap();
```

To see complete usage examples, refer to the [`examples/`](./examples) folder.

## Developing

This project uses [`just`](https://github.com/casey/just) for command running, and
[`cargo-rbmt`](https://github.com/rust-bitcoin/rust-bitcoin-maintainer-tools/tree/master/cargo-rbmt)
to manage everything related to `cargo`, such as formatting, linting, testing and CI. To install them, run:

```shell
~$ cargo install just

~$ cargo install cargo-rbmt
```

A `justfile` is provided for convenience. Run `just` to see available commands:

```shell
~$ just
> rustreexo
> A Rust implementation of Utreexo

Available recipes:
    bench BENCH="" # Run benchmarks: accumulator, proof, stump
    check          # Check code formatting, compilation, and linting [alias: c]
    check-sigs     # Checks whether all commits in this branch are signed [alias: cs]
    doc            # Generate documentation [alias: d]
    doc-open       # Generate and open documentation [alias: do]
    fmt            # Format code [alias: f]
    lock           # Regenerate Cargo-recent.lock and Cargo-minimal.lock [alias: l]
    pre-push       # Run pre-push suite: lock, fmt, check, test, and test-no-std [alias: p]
    test           # Run tests across all toolchains and lockfiles [alias: t]
    test-no-std    # Run no_std build check with the MSRV toolchain (1.74.0) [alias: tns]
```

## Minimum Supported Rust Version (MSRV)

This library should compile with any combination of features on Rust 1.74.0.

To build with the MSRV toolchain, copy `Cargo-minimal.lock` to `Cargo.lock`.

## License

Licensed under either of

* Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or <https://www.apache.org/licenses/LICENSE-2.0>)
* MIT license ([LICENSE-MIT](LICENSE-MIT) or <https://opensource.org/licenses/MIT>)

at your option.

## Contribution

Unless you explicitly state otherwise, any contribution intentionally
submitted for inclusion in the work by you, as defined in the Apache-2.0
license, shall be dual licensed as above, without any additional terms or
conditions.

## References

- [Utreexo: A dynamic hash-based accumulator optimized for the Bitcoin UTXO set](https://eprint.iacr.org/2019/611.pdf)
- [Dev++ 03-09-EN | Acumulator Based Cryptography & UTreexo](https://www.youtube.com/watch?v=xlKQP9J88uA)
- [What is UTreeXO? with Calvin Kim](https://www.youtube.com/watch?v=IcHW6RsZR7o)
- [rustreexo](https://blog.dlsouza.lol/bitcoin/utreexo/2023/07/07/rustreexo.html)
