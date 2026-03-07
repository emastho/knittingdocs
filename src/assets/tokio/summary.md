# Benchmark Summary

## Sources

- tokio: `results/tokio-1772893880154.csv`
- bun: `results/knitting-bun-1772893960039.csv`
- node: `results/knitting-node-1772894137705.csv`
- deno: `results/knitting-deno-1772894026138.csv`

## Batch Avg Latency (less is better)

```text
benchmark            | batch | tokio    | bun       | node     | deno     
---------------------+-------+----------+-----------+----------+----------
number f64 (8 bytes) | n=1   | 10.88 us | 5.51 us   | 4.96 us  | 8.53 us  
number f64 (8 bytes) | n=10  | 13.29 us | 8.59 us   | 7.93 us  | 6.85 us  
number f64 (8 bytes) | n=100 | 66.59 us | 36.59 us  | 35.27 us | 32.56 us 
large string 1 MiB   | n=1   | 26.11 us | 754.32 us | 1.97 ms  | 944.61 us
large string 1 MiB   | n=10  | 3.16 ms  | 3.59 ms   | 8.42 ms  | 7.36 ms  
large string 1 MiB   | n=100 | 34.98 ms | 39.12 ms  | 79.77 ms | 81.96 ms 
Uint8Array 1 MiB     | n=1   | 25.97 us | 378.58 us | 1.25 ms  | 793.45 us
Uint8Array 1 MiB     | n=10  | 3.18 ms  | 2.94 ms   | 3.38 ms  | 4.60 ms  
Uint8Array 1 MiB     | n=100 | 35.67 ms | 26.15 ms  | 35.17 ms | 41.39 ms 
```

## Batch P99 Latency (less is better)

```text
benchmark            | batch | tokio     | bun      | node      | deno     
---------------------+-------+-----------+----------+-----------+----------
number f64 (8 bytes) | n=1   | 11.99 us  | 15.13 us | 18.00 us  | 81.68 us 
number f64 (8 bytes) | n=10  | 15.30 us  | 19.95 us | 26.27 us  | 40.15 us 
number f64 (8 bytes) | n=100 | 103.83 us | 54.13 us | 129.17 us | 186.30 us
large string 1 MiB   | n=1   | 31.77 us  | 2.14 ms  | 5.06 ms   | 3.19 ms  
large string 1 MiB   | n=10  | 4.14 ms   | 6.43 ms  | 13.87 ms  | 26.49 ms 
large string 1 MiB   | n=100 | 38.19 ms  | 57.07 ms | 90.34 ms  | 115.31 ms
Uint8Array 1 MiB     | n=1   | 29.42 us  | 1.92 ms  | 1.67 ms   | 2.98 ms  
Uint8Array 1 MiB     | n=10  | 3.71 ms   | 4.95 ms  | 8.92 ms   | 13.92 ms 
Uint8Array 1 MiB     | n=100 | 39.82 ms  | 44.77 ms | 52.86 ms  | 62.99 ms 
```

## Avg Ratio Vs Tokio

```text
benchmark            | batch | bun/tokio | node/tokio | deno/tokio
---------------------+-------+-----------+------------+-----------
number f64 (8 bytes) | n=1   | 0.51x     | 0.46x      | 0.78x     
number f64 (8 bytes) | n=10  | 0.65x     | 0.60x      | 0.52x     
number f64 (8 bytes) | n=100 | 0.55x     | 0.53x      | 0.49x     
large string 1 MiB   | n=1   | 28.89x    | 75.34x     | 36.18x    
large string 1 MiB   | n=10  | 1.13x     | 2.66x      | 2.33x     
large string 1 MiB   | n=100 | 1.12x     | 2.28x      | 2.34x     
Uint8Array 1 MiB     | n=1   | 14.58x    | 48.31x     | 30.55x    
Uint8Array 1 MiB     | n=10  | 0.92x     | 1.06x      | 1.45x     
Uint8Array 1 MiB     | n=100 | 0.73x     | 0.99x      | 1.16x     
```

## Uint8Array Size Sweep Avg Latency (less is better)

```text
size    | tokio     | bun       | node      | deno     
--------+-----------+-----------+-----------+----------
8 B     | 37.15 us  | 57.49 us  | 76.64 us  | 57.24 us 
16 B    | 40.87 us  | 30.20 us  | 52.52 us  | 51.79 us 
32 B    | 38.96 us  | 48.35 us  | 45.04 us  | 46.93 us 
64 B    | 37.90 us  | 45.56 us  | 41.43 us  | 54.87 us 
128 B   | 39.51 us  | 38.28 us  | 45.97 us  | 48.66 us 
256 B   | 41.35 us  | 36.50 us  | 47.58 us  | 61.96 us 
512 B   | 39.88 us  | 58.65 us  | 94.81 us  | 75.70 us 
1 KiB   | 40.61 us  | 124.38 us | 132.68 us | 143.03 us
2 KiB   | 39.55 us  | 159.61 us | 101.86 us | 206.78 us
4 KiB   | 44.30 us  | 198.72 us | 260.71 us | 292.42 us
8 KiB   | 54.62 us  | 248.12 us | 259.46 us | 403.57 us
16 KiB  | 81.99 us  | 412.11 us | 439.41 us | 659.56 us
32 KiB  | 121.23 us | 725.50 us | 768.13 us | 1.22 ms  
64 KiB  | 1.73 ms   | 1.35 ms   | 1.41 ms   | 2.13 ms  
128 KiB | 3.89 ms   | 2.71 ms   | 2.83 ms   | 4.10 ms  
256 KiB | 8.51 ms   | 5.26 ms   | 5.75 ms   | 8.88 ms  
512 KiB | 17.58 ms  | 10.69 ms  | 12.53 ms  | 13.84 ms 
1 MiB   | 35.65 ms  | 22.58 ms  | 27.12 ms  | 32.01 ms 
```
