_default:
    @just --list

# Run benchmarks 
bench:
    cargo bench

# Build with all features
build:
    cargo build --all-features

# Check code formatting, compilation and linting
check:
    cargo +nightly fmt --all --check
    cargo +nightly check --all-features --all-targets --tests --benches
    cargo +nightly clippy --all-features --all-targets --tests --benches -- -D warnings
    RUSTDOCFLAGS="-D warnings" cargo +nightly doc --no-deps --all-features

# Format code
fmt:
    cargo +nightly fmt --all

# Run all tests
test:
    cargo test --all-features

# Run all tests on MSRV (1.63.0)
test-msrv:
    rm -f Cargo.lock
    cargo update -p criterion --precise 0.4.0
    cargo update -p rayon --precise 1.10.0
    cargo update -p rayon-core --precise 1.12.1
    cargo update -p serde_json --precise 1.0.81
    cargo update -p serde --precise 1.0.160
    cargo update -p regex --precise 1.9.6
    cargo update -p half --precise 2.2.1
    cargo update -p ppv-lite86 --precise 0.2.17
    cargo update -p textwrap --precise 0.16.0
    cargo update -p clap --precise 3.2.25
    cargo update -p syn --precise 2.0.32
    cargo update -p quote --precise 1.0.33
    
    cargo +1.63.0 test --all-features
    rm Cargo.lock

