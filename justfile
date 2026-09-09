alias c := check
alias cs := check-sigs
alias d := doc
alias do := doc-open
alias f := fmt
alias l := lock
alias t := test
alias tns := test-no-std
alias p := pre-push

_default:
    @echo "> rustreexo"
    @echo "> A Rust implementation of Utreexo\n"
    @just --list

[doc("Run this project's fuzz targets for 10 minutes per target by default")]
fuzz TARGET="" TIME="600":
    #!/usr/bin/env bash
    set -euo pipefail

    if [[ -n "{{TARGET}}" ]]; then
        cargo +nightly fuzz run "{{TARGET}}" -- -max_total_time={{TIME}}
    else
        for target in $(cargo +nightly fuzz list); do
            echo "Running fuzz target: $target"
            cargo +nightly fuzz run "$target" -- -max_total_time={{TIME}}
        done
    fi

[doc: "Run benchmarks: accumulator, proof, stump"]
bench BENCH="":
    cargo rbmt run bench {{ if BENCH != "" { "--bench " + BENCH } else { "" } }}

[doc: "Check code formatting, compilation, and linting"]
check:
    cargo rbmt fmt --check
    cargo rbmt lint
    cargo rbmt docsrs

[doc: "Checks whether all commits in this branch are signed"]
check-sigs:
    bash contrib/check-commit-signatures.sh

[doc: "Generate documentation"]
doc:
    cargo rbmt docsrs

[doc: "Generate and open documentation"]
doc-open:
    cargo rbmt docsrs --open

[doc: "Format code"]
fmt:
    cargo rbmt fmt

[doc: "Regenerate Cargo-recent.lock and Cargo-minimal.lock"]
lock:
    cargo rbmt lock

[doc: "Run tests across all toolchains and lockfiles"]
test:
    rustup target add thumbv7m-none-eabi
    cargo rbmt test --toolchain stable --lockfile recent
    cargo rbmt test --toolchain stable --lockfile minimal

[doc: "Run no_std build check with the MSRV toolchain (1.74.0)"]
test-no-std:
    rustup target add thumbv7m-none-eabi --toolchain 1.74.0
    cargo rbmt test --toolchain msrv --lockfile minimal

[doc: "Run pre-push suite: lock, fmt, check, test, and test-no-std"]
pre-push:
    @just check-sigs
    @just lock
    @just fmt
    @just check
    @just test
    @just test-no-std
