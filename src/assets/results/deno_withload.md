clk: ~3.72 GHz cpu: Apple M3 Ultra runtime: deno 2.6.6 (aarch64-apple-darwin)

| • knitting: primes up to 10,000,000 (chunk=250,000) | avg              | min         | p75         | p99         | max         |
| --------------------------------------------------- | ---------------- | ----------- | ----------- | ----------- | ----------- |
| main                                                | `931.23 ms/iter` | `929.41 ms` | `931.82 ms` | `934.58 ms` | `934.92 ms` |
| main + 1 extra threads → full range                 | `518.67 ms/iter` | `516.89 ms` | `519.92 ms` | `520.29 ms` | `520.38 ms` |
| main + 2 extra threads → full range                 | `368.10 ms/iter` | `366.24 ms` | `368.21 ms` | `369.24 ms` | `372.24 ms` |
| main + 3 extra threads → full range                 | `294.26 ms/iter` | `291.92 ms` | `295.24 ms` | `297.10 ms` | `297.73 ms` |
| main + 4 extra threads → full range                 | `253.56 ms/iter` | `250.74 ms` | `253.89 ms` | `256.49 ms` | `256.99 ms` |
