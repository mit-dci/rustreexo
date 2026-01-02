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

#[allow(clippy::unnecessary_cast)]
fn proof_creation(c: &mut Criterion) {
    let mut group = c.benchmark_group("proof_creation");

    for target_count in [1, 10].iter() {
        let targets: Vec<u64> = (0..*target_count).collect();
        let proof_hashes = generate_test_hashes((*target_count * 3) as usize, 42); // Approximate proof size

        group.throughput(Throughput::Elements(*target_count as u64));
        group.bench_with_input(
            BenchmarkId::new("new_proof", target_count),
            target_count,
            |b, _| {
                b.iter(|| {
                    let proof =
                        Proof::new(black_box(targets.clone()), black_box(proof_hashes.clone()));
                    black_box(proof)
                });
            },
        );
    }
    group.finish();
}

#[allow(clippy::unnecessary_cast)]
fn proof_verification(c: &mut Criterion) {
    let mut group = c.benchmark_group("proof_verification");

    // Setup a realistic scenario with an accumulator
    let accumulator_size = 100;
    let hashes = generate_test_hashes(accumulator_size, 42);
    let stump = Stump::new();
    let stump = stump.modify(&hashes, &[], &Proof::default()).unwrap();

    for target_count in [1, 10].iter() {
        let del_hashes = hashes[..*target_count].to_vec();
        let targets: Vec<u64> = (0..*target_count as u64).collect();

        // Create a realistic proof structure (simplified for benchmarking)
        let proof_hash_count = (*target_count as f64 * 3.5) as usize; // Realistic proof size
        let proof_hashes = generate_test_hashes(proof_hash_count, 123);
        let proof = Proof::new(targets, proof_hashes);

        group.throughput(Throughput::Elements(*target_count as u64));
        group.bench_with_input(
            BenchmarkId::new("verify", target_count),
            target_count,
            |b, _| {
                b.iter(|| {
                    let result = proof.verify(
                        black_box(&del_hashes),
                        black_box(&stump.roots),
                        black_box(stump.leaves),
                    );
                    black_box(result)
                });
            },
        );
    }
    group.finish();
}

criterion_group!(benches, proof_creation, proof_verification,);
criterion_main!(benches);
