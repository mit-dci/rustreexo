use std::hint::black_box;

use criterion::criterion_group;
use criterion::criterion_main;
use criterion::BenchmarkId;
use criterion::Criterion;
use criterion::Throughput;
use rand::rngs::StdRng;
use rand::Rng;
use rand::SeedableRng;
use rustreexo::accumulator::node_hash::BitcoinNodeHash;
use rustreexo::accumulator::proof::Proof;
use rustreexo::accumulator::stump::Stump;

fn generate_test_hashes(count: usize, seed: u64) -> Vec<BitcoinNodeHash> {
    let mut rng = StdRng::seed_from_u64(seed);
    (0..count)
        .map(|_| {
            let mut bytes = [0u8; 32];
            rng.fill(&mut bytes);
            BitcoinNodeHash::new(bytes)
        })
        .collect()
}

fn stump_modify_add_only(c: &mut Criterion) {
    let mut group = c.benchmark_group("stump_modify_add_only");

    for size in [10, 100].iter() {
        group.throughput(Throughput::Elements(*size as u64));
        group.bench_with_input(BenchmarkId::new("add_elements", size), size, |b, &size| {
            let hashes = generate_test_hashes(size, 42);
            let empty_proof = Proof::default();

            b.iter(|| {
                let stump = Stump::new();
                let result =
                    stump.modify(black_box(&hashes), black_box(&[]), black_box(&empty_proof));
                black_box(result.unwrap())
            });
        });
    }
    group.finish();
}

fn stump_verify(c: &mut Criterion) {
    let mut group = c.benchmark_group("stump_verify");

    // Setup: Create a stump with some elements and generate proofs
    let test_size = 1000;
    let hashes = generate_test_hashes(test_size, 42);
    let stump = Stump::new();
    let (stump, _) = stump.modify(&hashes, &[], &Proof::default()).unwrap();

    for proof_size in [1, 10, 100].iter() {
        let del_hashes = hashes[..*proof_size].to_vec();
        let proof = Proof::new(
            (0..*proof_size as u64).collect(),
            vec![], // Empty proof hashes for this benchmark
        );

        group.bench_with_input(
            BenchmarkId::new("verify_proof", proof_size),
            proof_size,
            |b, _| {
                b.iter(|| {
                    let result = stump.verify(black_box(&proof), black_box(&del_hashes));
                    black_box(result)
                });
            },
        );
    }
    group.finish();
}

criterion_group!(benches, stump_modify_add_only, stump_verify);
criterion_main!(benches);
