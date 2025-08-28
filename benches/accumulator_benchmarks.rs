use std::hint::black_box;

use criterion::criterion_group;
use criterion::criterion_main;
use criterion::BenchmarkId;
use criterion::Criterion;
use criterion::Throughput;
use rand::rngs::StdRng;
use rand::Rng;
use rand::SeedableRng;
use rustreexo::accumulator::mem_forest::MemForest;
use rustreexo::accumulator::node_hash::BitcoinNodeHash;
use rustreexo::accumulator::pollard::Pollard;

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

fn memforest_proof_generation(c: &mut Criterion) {
    let mut group = c.benchmark_group("memforest_proof_generation");

    let accumulator_size = 100;
    let hashes = generate_test_hashes(accumulator_size, 42);
    let mut forest = MemForest::new();
    forest.modify(&hashes, &[]).unwrap();

    for target_count in [1, 10].iter() {
        let targets = &hashes[..*target_count];

        group.throughput(Throughput::Elements(*target_count as u64));
        group.bench_with_input(
            BenchmarkId::new("generate_proof", target_count),
            target_count,
            |b, _| {
                b.iter(|| {
                    let result = forest.prove(black_box(targets));
                    black_box(result.unwrap())
                });
            },
        );
    }
    group.finish();
}

fn memforest_verification(c: &mut Criterion) {
    let mut group = c.benchmark_group("memforest_verification");

    let accumulator_size = 100;
    let hashes = generate_test_hashes(accumulator_size, 42);
    let mut forest = MemForest::new();
    forest.modify(&hashes, &[]).unwrap();

    for target_count in [1, 10].iter() {
        let targets = &hashes[..*target_count];
        let proof = forest.prove(targets).unwrap();

        group.throughput(Throughput::Elements(*target_count as u64));
        group.bench_with_input(
            BenchmarkId::new("verify_proof", target_count),
            target_count,
            |b, _| {
                b.iter(|| {
                    let result = forest.verify(black_box(&proof), black_box(targets));
                    black_box(result.unwrap())
                });
            },
        );
    }
    group.finish();
}

fn pollard_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("pollard_operations");

    let base_size = 100;
    let hashes = generate_test_hashes(base_size, 42);
    let roots = vec![hashes[0]]; // Simplified root structure
    let pollard = Pollard::from_roots(roots, base_size as u64);

    {
        let batch_size = &10;
        let _del_hashes = &hashes[..*batch_size / 2];

        group.throughput(Throughput::Elements(*batch_size as u64));
        group.bench_with_input(
            BenchmarkId::new("pollard_roots", batch_size),
            batch_size,
            |b, _| {
                b.iter(|| {
                    let roots = pollard.roots();
                    black_box(roots.len())
                });
            },
        );

        group.bench_with_input(
            BenchmarkId::new("pollard_leaves", batch_size),
            batch_size,
            |b, _| {
                b.iter(|| {
                    let leaves = pollard.leaves();
                    black_box(leaves)
                });
            },
        );
    }
    group.finish();
}

criterion_group!(
    benches,
    memforest_proof_generation,
    memforest_verification,
    pollard_operations,
);
criterion_main!(benches);
