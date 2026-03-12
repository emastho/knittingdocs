clk: ~3.69 GHz
cpu: Apple M3 Ultra
runtime: bun 1.3.6 (arm64-darwin)

| • knitting: primes up to 10,000,000 (chunk=250,000) |              avg |         min |         p75 |         p99 |         max |
| ----------------------------------- | ---------------- | ----------- | ----------- | ----------- | ----------- |
| main                                | `572.57 ms/iter` | `569.05 ms` | `573.73 ms` | `576.83 ms` | `577.70 ms` |
| main + 1 extra threads → full range | `304.05 ms/iter` | `299.51 ms` | `305.94 ms` | `310.39 ms` | `310.63 ms` |
| main + 2 extra threads → full range | `224.68 ms/iter` | `220.21 ms` | `228.08 ms` | `230.10 ms` | `230.84 ms` |
| main + 3 extra threads → full range | `179.33 ms/iter` | `174.37 ms` | `181.15 ms` | `181.78 ms` | `182.35 ms` |
| main + 4 extra threads → full range | `157.48 ms/iter` | `153.46 ms` | `159.02 ms` | `159.85 ms` | `160.47 ms` |
