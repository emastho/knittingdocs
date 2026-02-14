clk: ~3.81 GHz cpu: Apple M3 Ultra runtime: bun 1.3.6 (arm64-darwin)

| • knitting: primes up to 10,000,000 (chunk=250,000) | avg              | min         | p75         | p99         | max         |
| --------------------------------------------------- | ---------------- | ----------- | ----------- | ----------- | ----------- |
| main                                                | `556.95 ms/iter` | `551.08 ms` | `559.05 ms` | `559.73 ms` | `560.13 ms` |
| main + 1 extra threads → full range                 | `310.72 ms/iter` | `308.29 ms` | `311.82 ms` | `314.36 ms` | `314.82 ms` |
| main + 2 extra threads → full range                 | `225.28 ms/iter` | `222.10 ms` | `226.22 ms` | `227.96 ms` | `228.48 ms` |
| main + 3 extra threads → full range                 | `171.31 ms/iter` | `169.19 ms` | `171.86 ms` | `172.62 ms` | `172.71 ms` |
| main + 4 extra threads → full range                 | `145.30 ms/iter` | `141.00 ms` | `147.25 ms` | `147.44 ms` | `149.24 ms` |
