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

# Format code
fmt:
    cargo +nightly fmt --all

# Run all tests
test:
    cargo test --all-features
