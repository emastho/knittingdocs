clk: ~3.74 GHz
cpu: Apple M3 Ultra
runtime: bun 1.3.6 (arm64-darwin)

| • knitting: primes up to 10,000,000 (chunk=250,000) |              avg |         min |         p75 |         p99 |         max |
| ----------------------------------- | ---------------- | ----------- | ----------- | ----------- | ----------- |
| main                                | `564.51 ms/iter` | `551.66 ms` | `570.70 ms` | `571.76 ms` | `572.48 ms` |
| main + 1 extra threads → full range | `311.94 ms/iter` | `308.28 ms` | `314.37 ms` | `315.97 ms` | `316.11 ms` |
| main + 2 extra threads → full range | `226.64 ms/iter` | `224.54 ms` | `228.11 ms` | `228.74 ms` | `230.69 ms` |
| main + 3 extra threads → full range | `173.87 ms/iter` | `170.92 ms` | `175.81 ms` | `175.94 ms` | `176.80 ms` |
| main + 4 extra threads → full range | `145.99 ms/iter` | `143.87 ms` | `146.60 ms` | `147.75 ms` | `148.29 ms` |
