clk: ~3.61 GHz
cpu: Apple M3 Ultra
runtime: deno 2.6.6 (aarch64-apple-darwin)

| • knitting: primes up to 10,000,000 (chunk=250,000) |              avg |         min |         p75 |         p99 |         max |
| ----------------------------------- | ---------------- | ----------- | ----------- | ----------- | ----------- |
| main                                | `956.62 ms/iter` | `950.73 ms` | `957.55 ms` | `959.96 ms` | `963.62 ms` |
| main + 1 extra threads → full range | `496.69 ms/iter` | `492.92 ms` | `497.48 ms` | `501.54 ms` | `501.70 ms` |
| main + 2 extra threads → full range | `360.28 ms/iter` | `355.94 ms` | `361.84 ms` | `364.48 ms` | `366.29 ms` |
| main + 3 extra threads → full range | `292.60 ms/iter` | `288.34 ms` | `293.62 ms` | `296.29 ms` | `300.23 ms` |
| main + 4 extra threads → full range | `254.74 ms/iter` | `251.74 ms` | `256.04 ms` | `256.66 ms` | `258.82 ms` |
