clk: ~3.65 GHz
cpu: Apple M3 Ultra
runtime: deno 2.6.6 (aarch64-apple-darwin)

| • knitting: primes up to 10,000,000 (chunk=250,000) |              avg |         min |         p75 |         p99 |         max |
| ----------------------------------- | ---------------- | ----------- | ----------- | ----------- | ----------- |
| main                                | `944.29 ms/iter` | `938.88 ms` | `946.93 ms` | `948.07 ms` | `948.93 ms` |
| main + 1 extra threads → full range | `518.26 ms/iter` | `516.62 ms` | `519.29 ms` | `519.76 ms` | `520.20 ms` |
| main + 2 extra threads → full range | `369.63 ms/iter` | `367.15 ms` | `369.86 ms` | `372.35 ms` | `375.12 ms` |
| main + 3 extra threads → full range | `295.31 ms/iter` | `291.73 ms` | `296.01 ms` | `297.72 ms` | `300.74 ms` |
| main + 4 extra threads → full range | `254.91 ms/iter` | `252.66 ms` | `255.19 ms` | `256.57 ms` | `258.93 ms` |
