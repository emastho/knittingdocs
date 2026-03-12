clk: ~3.72 GHz
cpu: Apple M3 Ultra
runtime: node 24.12.0 (arm64-darwin)

| • knitting: primes up to 10,000,000 (chunk=250,000) |              avg |         min |         p75 |         p99 |         max |
| ----------------------------------- | ---------------- | ----------- | ----------- | ----------- | ----------- |
| main                                | `959.14 ms/iter` | `955.16 ms` | `959.93 ms` | `961.89 ms` | `963.68 ms` |
| main + 1 extra threads → full range | `538.28 ms/iter` | `531.37 ms` | `539.87 ms` | `541.65 ms` | `547.02 ms` |
| main + 2 extra threads → full range | `401.87 ms/iter` | `395.43 ms` | `404.32 ms` | `406.77 ms` | `408.40 ms` |
| main + 3 extra threads → full range | `317.52 ms/iter` | `311.27 ms` | `319.14 ms` | `323.94 ms` | `327.36 ms` |
| main + 4 extra threads → full range | `274.21 ms/iter` | `270.63 ms` | `276.88 ms` | `278.30 ms` | `279.69 ms` |
