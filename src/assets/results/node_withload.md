clk: ~3.72 GHz
cpu: Apple M3 Ultra
runtime: node 24.12.0 (arm64-darwin)

| • knitting: primes up to 10,000,000 (chunk=250,000) |              avg |         min |         p75 |         p99 |         max |
| ----------------------------------- | ---------------- | ----------- | ----------- | ----------- | ----------- |
| main                                | `943.33 ms/iter` | `927.86 ms` | `945.92 ms` | `947.41 ms` | `953.31 ms` |
| main + 1 extra threads → full range | `546.61 ms/iter` | `541.94 ms` | `547.44 ms` | `551.77 ms` | `552.63 ms` |
| main + 2 extra threads → full range | `400.50 ms/iter` | `395.92 ms` | `402.01 ms` | `402.97 ms` | `404.10 ms` |
| main + 3 extra threads → full range | `311.25 ms/iter` | `307.31 ms` | `311.97 ms` | `317.19 ms` | `317.75 ms` |
| main + 4 extra threads → full range | `263.77 ms/iter` | `259.23 ms` | `266.50 ms` | `270.15 ms` | `271.66 ms` |
