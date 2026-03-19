# Benchmark Summary

## Sources

- tokio: `results/tokio-1773827721825.csv`
- bun: `results/knitting-bun-1773827812276.csv`
- node: `results/knitting-node-1773828074699.csv`
- deno: `results/knitting-deno-1773827925019.csv`

## Machine Specs

- OS: Ubuntu 23.10
- Kernel: 6.5.0-44-generic
- Architecture: x86_64
- CPU: AMD Ryzen 7 4700U with Radeon Graphics
- Topology: 8 logical CPUs, 1 socket(s), 8 core(s)/socket, 1 thread(s)/core
- Memory: 15.1 GiB
- Swap: 4.0 GiB

## Methodology Notes

- The main string and byte benchmarks are intended to compare the same logical round trip on both sides: send payload, receive it in the worker, echo it back, receive it again on the caller, then wait for the whole batch.
- In `src/main.ts`, the `string` and `Uint8Array` paths go through knitting transport in both directions. That transport materializes a fresh payload on receive, so the round trip includes payload work on both the request side and the reply side.
- To keep the Tokio baseline fair, `src/main.rs` clones `String` and `Vec<u8>` on send and also clones again on the worker reply. The reply clone is intentional. Without it, Tokio would be measuring a cheaper return-path move while the JS runtimes were still paying for fresh payload materialization on the way back.
- The `Arc<Vec<u8>>` sweep is intentionally separate and is not the default apples-to-apples byte benchmark. It exists as an upper-bound shared-bytes reference for small payloads. `Arc::clone` only bumps a refcount, so it is expected to be cheaper than copying bytes.
- This means the default `string` and `Uint8Array` tables should be read as the fairer comparison, while the Arc section should be read as "how close does the normal transport get to shared ownership for small values?"

## Batch Avg Latency (less is better)

```text
benchmark            | batch | tokio     | bun      | node     | deno    
---------------------+-------+-----------+----------+----------+---------
number f64 (8 bytes) | n=1   | 13.01 us  | 7.35 us  | 6.63 us  | 21.54 us
number f64 (8 bytes) | n=10  | 27.50 us  | 13.41 us | 17.28 us | 11.97 us
number f64 (8 bytes) | n=100 | 89.55 us  | 80.61 us | 62.33 us | 63.28 us
large string 1 MiB   | n=1   | 221.35 us | 1.19 ms  | 2.85 ms  | 1.38 ms 
large string 1 MiB   | n=10  | 6.20 ms   | 6.01 ms  | 10.79 ms | 10.38 ms
large string 1 MiB   | n=100 | 37.93 ms  | 50.16 ms | 84.66 ms | 83.90 ms
Uint8Array 1 MiB     | n=1   | 272.81 us | 1.30 ms  | 2.35 ms  | 1.14 ms 
Uint8Array 1 MiB     | n=10  | 4.64 ms   | 5.27 ms  | 5.22 ms  | 6.36 ms 
Uint8Array 1 MiB     | n=100 | 37.83 ms  | 47.76 ms | 54.95 ms | 60.04 ms
```

## Batch P99 Latency (less is better)

```text
benchmark            | batch | tokio     | bun      | node      | deno     
---------------------+-------+-----------+----------+-----------+----------
number f64 (8 bytes) | n=1   | 16.85 us  | 18.70 us | 26.25 us  | 160.57 us
number f64 (8 bytes) | n=10  | 40.83 us  | 36.58 us | 81.26 us  | 111.89 us
number f64 (8 bytes) | n=100 | 203.57 us | 92.37 us | 314.11 us | 263.05 us
large string 1 MiB   | n=1   | 371.10 us | 3.74 ms  | 3.73 ms   | 2.97 ms  
large string 1 MiB   | n=10  | 8.44 ms   | 8.41 ms  | 15.75 ms  | 14.45 ms 
large string 1 MiB   | n=100 | 40.81 ms  | 61.62 ms | 105.51 ms | 106.67 ms
Uint8Array 1 MiB     | n=1   | 400.45 us | 3.03 ms  | 5.58 ms   | 5.81 ms  
Uint8Array 1 MiB     | n=10  | 8.41 ms   | 7.80 ms  | 9.52 ms   | 14.37 ms 
Uint8Array 1 MiB     | n=100 | 43.71 ms  | 59.77 ms | 72.39 ms  | 81.71 ms 
```

## Avg Ratio Vs Tokio

```text
benchmark            | batch | bun/tokio | node/tokio | deno/tokio
---------------------+-------+-----------+------------+-----------
number f64 (8 bytes) | n=1   | 0.56x     | 0.51x      | 1.66x     
number f64 (8 bytes) | n=10  | 0.49x     | 0.63x      | 0.44x     
number f64 (8 bytes) | n=100 | 0.90x     | 0.70x      | 0.71x     
large string 1 MiB   | n=1   | 5.36x     | 12.86x     | 6.22x     
large string 1 MiB   | n=10  | 0.97x     | 1.74x      | 1.68x     
large string 1 MiB   | n=100 | 1.32x     | 2.23x      | 2.21x     
Uint8Array 1 MiB     | n=1   | 4.75x     | 8.62x      | 4.18x     
Uint8Array 1 MiB     | n=10  | 1.13x     | 1.12x      | 1.37x     
Uint8Array 1 MiB     | n=100 | 1.26x     | 1.45x      | 1.59x     
```

## Uint8Array Size Sweep Avg Latency (less is better)

```text
size    | tokio     | bun       | node      | deno     
--------+-----------+-----------+-----------+----------
8 B     | 82.99 us  | 62.80 us  | 88.20 us  | 107.01 us
16 B    | 81.91 us  | 56.24 us  | 65.37 us  | 95.78 us 
32 B    | 85.70 us  | 49.48 us  | 65.76 us  | 85.05 us 
64 B    | 76.98 us  | 42.68 us  | 66.88 us  | 78.27 us 
128 B   | 92.53 us  | 53.53 us  | 79.28 us  | 84.39 us 
256 B   | 99.70 us  | 63.42 us  | 83.89 us  | 100.44 us
512 B   | 86.67 us  | 68.55 us  | 97.07 us  | 118.03 us
1 KiB   | 101.42 us | 171.09 us | 157.61 us | 169.50 us
2 KiB   | 191.25 us | 194.62 us | 220.68 us | 233.39 us
4 KiB   | 195.56 us | 260.16 us | 324.39 us | 391.43 us
8 KiB   | 208.84 us | 397.05 us | 465.89 us | 539.98 us
16 KiB  | 279.25 us | 649.18 us | 741.47 us | 899.81 us
32 KiB  | 1.48 ms   | 1.14 ms   | 1.27 ms   | 1.41 ms  
64 KiB  | 2.71 ms   | 2.38 ms   | 2.49 ms   | 2.89 ms  
128 KiB | 5.66 ms   | 5.02 ms   | 5.11 ms   | 6.08 ms  
256 KiB | 11.92 ms  | 10.56 ms  | 10.11 ms  | 11.96 ms 
512 KiB | 23.06 ms  | 22.33 ms  | 22.66 ms  | 25.26 ms 
1 MiB   | 29.48 ms  | 46.97 ms  | 52.53 ms  | 55.77 ms 
```

## Arc Comparison Size Sweep Avg Latency (less is better)

Tokio uses `Arc<Vec<u8>>` here as a separate shared-bytes reference point, not the default apples-to-apples byte path.

```text
size  | tokio    | bun      | node     | deno     
------+----------+----------+----------+----------
8 B   | 80.76 us | 70.31 us | 86.19 us | 97.79 us 
16 B  | 79.35 us | 60.94 us | 73.73 us | 77.46 us 
32 B  | 81.48 us | 57.04 us | 70.26 us | 77.03 us 
64 B  | 80.14 us | 54.44 us | 75.94 us | 78.81 us 
128 B | 79.89 us | 68.50 us | 82.51 us | 85.95 us 
256 B | 79.48 us | 50.59 us | 85.94 us | 100.10 us
512 B | 79.51 us | 74.78 us | 97.23 us | 123.11 us
```

## Arc Comparison Avg Ratio Vs Tokio

```text
size  | bun/tokio | node/tokio | deno/tokio
------+-----------+------------+-----------
8 B   | 0.87x     | 1.07x      | 1.21x     
16 B  | 0.77x     | 0.93x      | 0.98x     
32 B  | 0.70x     | 0.86x      | 0.95x     
64 B  | 0.68x     | 0.95x      | 0.98x     
128 B | 0.86x     | 1.03x      | 1.08x     
256 B | 0.64x     | 1.08x      | 1.26x     
512 B | 0.94x     | 1.22x      | 1.55x     
```
