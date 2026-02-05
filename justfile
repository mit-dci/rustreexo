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

    cargo +nightly check --no-default-features --all-targets
    cargo +nightly check --all-features --all-targets
    cargo +nightly clippy --no-default-features --all-targets -- -D warnings
    cargo +nightly clippy --all-features --all-targets -- -D warnings

    RUSTDOCFLAGS="-D warnings" cargo +nightly doc --no-deps --all-features

# Format code
fmt:
    cargo +nightly fmt --all

# Run all tests with stable and nightly toolchains
test:
    @just test-stable
    @just test-nightly

# Run all tests with a stable toolchain
test-stable:
    cargo +stable test --no-default-features
    cargo +stable test --all-features

# Run all tests with a nightly toolchain
test-nightly:
    cargo +nightly test --no-default-features
    cargo +nightly test --all-features

# Run all tests on MSRV (1.74.0)
test-msrv:
    rm -f Cargo.lock
    cargo update -p criterion --precise 0.5.1
    cargo update -p rayon --precise 1.10.0
    cargo update -p rayon-core --precise 1.12.1
    cargo update -p serde_json --precise 1.0.81
    cargo update -p serde --precise 1.0.160
    cargo update -p half --precise 2.4.1

    cargo +1.74.0 test --no-default-features
    cargo +1.74.0 test --all-features
    rm Cargo.lock
