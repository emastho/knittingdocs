clk: ~3.82 GHz cpu: Apple M3 Ultra runtime: node 24.12.0 (arm64-darwin)

| • knitting: primes up to 10,000,000 (chunk=250,000) | avg              | min         | p75         | p99         | max         |
| --------------------------------------------------- | ---------------- | ----------- | ----------- | ----------- | ----------- |
| main                                                | `931.32 ms/iter` | `928.52 ms` | `932.10 ms` | `935.14 ms` | `936.57 ms` |
| main + 1 extra threads → full range                 | `547.76 ms/iter` | `545.30 ms` | `548.21 ms` | `549.95 ms` | `551.20 ms` |
| main + 2 extra threads → full range                 | `401.18 ms/iter` | `398.68 ms` | `401.83 ms` | `402.17 ms` | `403.56 ms` |
| main + 3 extra threads → full range                 | `311.02 ms/iter` | `308.38 ms` | `310.94 ms` | `313.06 ms` | `317.46 ms` |
| main + 4 extra threads → full range                 | `262.38 ms/iter` | `260.86 ms` | `262.92 ms` | `262.97 ms` | `264.36 ms` |
