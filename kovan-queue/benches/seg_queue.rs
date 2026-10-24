//! `SegQueue` throughput and latency.
//!
//! - `seg_queue_single`: one thread. `push_pop` is one push and one pop of
//!   one value; `fill_drain` pushes 4096 values then pops them (128 segments
//!   allocated, filled and retired per iteration); `pop_empty`, `try_pop_empty`
//!   and `is_empty` poll an empty queue; `len` reads a queue holding 100 values.
//! - `seg_queue_contended`: producers and consumers on their own threads,
//!   started together behind a barrier, `TOTAL` values in all. `spsc` is one
//!   of each, `mpsc_N` N producers and one consumer, `mpmc_NxN` N of each.
//!   Each consumer pops its share, spinning on `None`; the time is from the
//!   barrier to the last thread's end.

use criterion::{BenchmarkId, Criterion, Throughput, criterion_group, criterion_main};
use kovan_queue::seg_queue::SegQueue;
use std::hint::black_box;
use std::sync::{Arc, Barrier};
use std::thread;
use std::time::{Duration, Instant};

const TOTAL: u64 = 1 << 17;
const FILL: u64 = 4096;

fn single(c: &mut Criterion) {
    let mut group = c.benchmark_group("seg_queue_single");

    group.throughput(Throughput::Elements(1));
    group.bench_function("push_pop", |b| {
        let q = SegQueue::new();
        b.iter(|| {
            q.push(black_box(1u64));
            black_box(q.pop())
        });
    });

    group.bench_function("pop_empty", |b| {
        let q = SegQueue::<u64>::new();
        b.iter(|| black_box(q.pop()));
    });

    group.bench_function("try_pop_empty", |b| {
        let q = SegQueue::<u64>::new();
        b.iter(|| black_box(q.try_pop().ok()));
    });

    group.bench_function("is_empty", |b| {
        let q = SegQueue::<u64>::new();
        b.iter(|| black_box(q.is_empty()));
    });

    group.bench_function("len", |b| {
        let q = SegQueue::new();
        for i in 0..100u64 {
            q.push(i);
        }
        b.iter(|| black_box(q.len()));
    });

    group.throughput(Throughput::Elements(FILL));
    group.bench_function("fill_drain", |b| {
        let q = SegQueue::new();
        b.iter(|| {
            for i in 0..FILL {
                q.push(black_box(i));
            }
            for _ in 0..FILL {
                black_box(q.pop());
            }
        });
    });

    group.finish();
}

/// One run: `producers` threads push `TOTAL` values in all, `consumers`
/// threads pop them. Returns the time from the common start to the end.
fn run(producers: u64, consumers: u64) -> Duration {
    let q = Arc::new(SegQueue::new());
    let start = Arc::new(Barrier::new((producers + consumers + 1) as usize));
    let per_producer = TOTAL / producers;
    let per_consumer = TOTAL / consumers;
    let mut handles = Vec::new();
    for p in 0..producers {
        let q = Arc::clone(&q);
        let start = Arc::clone(&start);
        handles.push(thread::spawn(move || {
            start.wait();
            for i in 0..per_producer {
                q.push(p * per_producer + i);
            }
        }));
    }
    for _ in 0..consumers {
        let q = Arc::clone(&q);
        let start = Arc::clone(&start);
        handles.push(thread::spawn(move || {
            start.wait();
            let mut got = 0;
            while got < per_consumer {
                match q.pop() {
                    Some(v) => {
                        black_box(v);
                        got += 1;
                    }
                    None => std::hint::spin_loop(),
                }
            }
        }));
    }
    start.wait();
    let t0 = Instant::now();
    for h in handles {
        h.join().unwrap();
    }
    t0.elapsed()
}

fn contended(c: &mut Criterion) {
    let mut group = c.benchmark_group("seg_queue_contended");
    group.sample_size(20);
    group.measurement_time(Duration::from_secs(8));
    group.throughput(Throughput::Elements(TOTAL));
    let shapes: [(&str, u64, u64); 7] = [
        ("spsc", 1, 1),
        ("mpsc_2", 2, 1),
        ("mpsc_4", 4, 1),
        ("mpsc_8", 8, 1),
        ("mpmc_2x2", 2, 2),
        ("mpmc_4x4", 4, 4),
        ("mpmc_8x8", 8, 8),
    ];
    for (name, producers, consumers) in shapes {
        group.bench_function(BenchmarkId::from_parameter(name), |b| {
            b.iter_custom(|iters| (0..iters).map(|_| run(producers, consumers)).sum());
        });
    }
    group.finish();
}

criterion_group!(benches, single, contended);
criterion_main!(benches);
