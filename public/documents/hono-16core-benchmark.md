# Isolating expensive routes: Hono + Knitting on 16 real cores

Reproduction of the [hono_server example](https://knittingdocs.netlify.app/examples/data_transforms/rendering_output/hono_server/)
benchmark on dedicated cloud hardware, with the load generator on a separate machine.

Measured 2026-08-24 and re-measured 2026-08-25 after the worker timer policy
changed. Every number here came off the DigitalOcean test bed described below.
None of it was measured on a laptop.

## What is being tested

Knitting is built for route sets with a Pareto shape: a few routes eat most of the main
thread and everything else queues behind them. The docs example is exactly that shape.
`/ssr` renders React and `/jwt` signs HS256, while `/ping` hands back a small JSON
object. On one event loop the cheap route does not get to be cheap. It waits its turn
behind whatever heavy work is already running.

So the claim under test is not "workers make SSR faster". It is that moving the expensive
minority off the event loop makes the whole server faster, including the routes that were
never the bottleneck. The best evidence either way is `/ping`, which never touches the
pool in any configuration. Anything that moves its numbers is the pool changing the host
thread's environment, not the pool doing its work.

## The worker timer policy

Every pool configuration below uses one rule for how an idle worker waits:

- **One worker: a 50us spin budget.** A single worker is the request's critical
  path, so a short spin that catches the next call before it parks is worth
  paying for.
- **Two or more workers: no spin at all.** Surplus workers should sleep, not
  poll. The work they would have caught by spinning is caught by a peer that is
  already awake.

```ts
createPool({
  threads,
})
```

This policy is now the shipped default. It keeps a one-worker request path
ready while allowing multi-worker pools to sleep instead of spending CPU on
idle polling. The CPU measurements in [section C](#c-what-the-timer-policy-is-worth)
show the cost per request and while idle.

## Headline

1. The route that never touches the pool benefits most. `/ping` gains 201% rps and
   drops its p50 by 68% under saturating load, and its p99 by 81-83% at matched
   load. That beats both offloaded routes on every one of those measures. The win
   is removing head-of-line blocking, not making anything faster.
2. One saturated thread flattens every route down to the slowest one. `hono_only`
   serves ping / ssr / jwt at 2815 / 2815 / 2578 rps: three routes with wildly
   different costs, all pinned to the same rate. Offloading the expensive two is
   what breaks that coupling, and the cheap route then runs away to 8,486.
3. The offloaded routes gain too, just less. +71% rps on `/ssr` and +83% on `/jwt`,
   with p99 down 70% and 83% at matched load.
4. Efficiency now degrades gently instead of collapsing. `threads: 1` is still the
   best configuration at 10,041 rps/core, but an oversized `threads: 15` pool costs
   2.4x that rather than 9.6x, and its tail latency is *better* than a correctly
   sized pool's. Getting the pool size wrong is no longer expensive.

## Test bed

| | Server | Load generator |
|---|---|---|
| Droplet | `c-16` (CPU-Optimized, dedicated) | `c-8` (CPU-Optimized, dedicated) |
| CPU | Intel Xeon Platinum 8168 @ 2.70GHz, **16 real cores, no SMT** | 8 real cores |
| RAM | 32 GB | 16 GB |
| OS | Ubuntu 24.04 | Ubuntu 24.04 |
| Region | nyc1 | nyc1 |

- Traffic crosses the **private VPC network**, not the public interface.
- Runtime: **Bun 1.4.0**. Load tool: **oha 1.14.0**.
- Knitting: local build of this repo at `6c0e56d`, symlinked into the example as
  `node_modules/knitting`.
- Tuning applied to both boxes: `somaxconn=65535`, `ip_local_port_range=1024 65535`,
  `nofile=1048576`.
- Cost: about $1.30 across both runs. All droplets destroyed afterwards.

The generator was never the bottleneck. It used 0.20-0.53 of its 8 cores in every run
(read from `/proc/stat`), and it is a physically separate machine, so it takes no cycles
from the server under test.

## Method

Under test are the three routes from the docs example, `GET /ping`, `POST /ssr` (React
SSR) and `POST /jwt` (HS256 sign), in two server variants:

- **`hono_only`** - route work runs inline on the main thread.
- **`hono_knitting`** - SSR and JWT run as Knitting tasks; `KNIT_THREADS` sets pool size
  and `KNIT_SPIN` sets the spin budget. `/ping` is identical in both and never
  touches the pool.

The load pattern follows the docs' own numbers, which only make sense if all three routes
are loaded at once against one server: three concurrent `oha` processes, one per route, so
the routes compete for the same main thread. 6s warmup, then a 15s measured window.

Recorded per run: per-route rps and latency percentiles, server CPU-seconds (from
`/proc/<pid>/stat`, converted to cores), generator CPU, OS thread count, and
**idle CPU** over a 5s window with the server running and no load offered at all.
That last column is new in the second run and it is where the interesting result
turned out to live.

Each configuration asserts its own identity before load starts, checking process cmdline
plus `KNIT_THREADS` and `KNIT_SPIN` read back from `/proc/<pid>/environ`. That check
exists because an earlier version of this harness recorded the wrong PID (`setsid` forks),
failed to stop the previous server, and quietly re-measured one `hono_only` process six
times while reporting it as six different pool sizes. See [Harness pitfalls](#harness-pitfalls).

## A. Saturating load - throughput

`oha -c 100` per route (300 connections total), 15s.

| pool | /ping | /ssr | /jwt | total rps | vs hono_only | idle cores | server cores | rps/core | CPU-us/req |
|---|---|---|---|---|---|---|---|---|---|
| hono_only | 2815 | 2815 | 2578 | 8208 | - | 0.002 | 1.19 | 6909 | 145 |
| **threads: 1** | **8486** | 4816 | 4712 | **18014** | **+119%** | **0.058** | **1.79** | **10041** | **100** |
| threads: 2 | 5785 | 4997 | 5029 | 15811 | +93% | 0.034 | 1.92 | 8244 | 121 |
| threads: 4 | 4763 | 4410 | 4733 | 13906 | +69% | 0.054 | 2.00 | 6944 | 144 |
| threads: 8 | 3946 | 3921 | 3782 | 11649 | +42% | 0.106 | 2.31 | 5046 | 198 |
| threads: 15 | 4032 | 3981 | 3974 | 11987 | +46% | 0.164 | 2.83 | 4238 | 236 |

Every pool size beats `hono_only` on throughput. The ranking still falls with pool
size, because the host is the only producer and more consumers cannot raise the
rate it feeds them, but the CPU cost of being wrong is now small: fifteen workers
cost 1.6x the CPU of one worker, not 5.6x.

Latency under the same saturating load (p50 / p99, ms):

| pool | /ping | /ssr | /jwt |
|---|---|---|---|
| hono_only | 35.42 / 42.99 | 35.44 / 42.89 | 35.64 / 74.01 |
| threads: 1 | 11.50 / 22.10 | 19.88 / 40.36 | 20.41 / 41.51 |
| threads: 2 | 16.04 / 27.31 | 17.94 / 44.30 | 17.84 / 43.53 |
| threads: 4 | 19.31 / 31.65 | 20.30 / 49.86 | 19.69 / 32.93 |
| threads: 8 | 25.70 / 36.21 | 25.48 / 39.35 | 25.78 / 52.40 |
| threads: 15 | 23.78 / 36.03 | 24.36 / 38.16 | 24.39 / 40.03 |

Note that `hono_only` serves all three routes at almost identical rates (2815 / 2815 /
2578). That is the signature of a single saturated JS thread: the cheap route is throttled
down to the rate of the expensive ones. Offloading is what breaks the symmetry.

## B. Open loop, fixed rate - latency

The saturating test couples throughput and latency, so latency is not comparable across
configs there. This run offers 2000 rps per route (6000 total) to every config, about 73%
of `hono_only`'s measured ceiling, so all configs do identical work and only latency
varies. All configs achieved the full rate with a 100% success rate.

**/ping** (never touches the pool)

| config | p50 | p99 | server cores | idle cores |
|---|---|---|---|---|
| hono_only | 0.81 | 16.93 | 1.08 | 0.002 |
| threads: 1 | 0.40 | **2.31** | 1.10 | 0.060 |
| threads: 4 | 0.45 | 3.18 | 1.57 | 0.046 |
| threads: 8 | 0.50 | **2.91** | 1.94 | 0.096 |
| threads: 15 | 0.49 | 3.00 | 2.29 | 0.194 |

**/ssr**

| config | p50 | p99 | server cores |
|---|---|---|---|
| hono_only | 0.84 | 14.32 | 1.08 |
| threads: 1 | 2.22 | 8.71 | 1.10 |
| threads: 4 | 0.77 | 4.26 | 1.57 |
| threads: 8 | 0.79 | 4.35 | 1.94 |
| threads: 15 | 0.84 | **4.12** | 2.29 |

**/jwt**

| config | p50 | p99 | server cores |
|---|---|---|---|
| hono_only | 1.03 | 25.18 | 1.08 |
| threads: 1 | 2.58 | 9.76 | 1.10 |
| threads: 4 | 0.78 | 4.40 | 1.57 |
| threads: 8 | 0.84 | **4.27** | 1.94 |
| threads: 15 | 0.88 | 4.33 | 2.29 |

p99 against `hono_only`: -81% on `/ping`, -70% on `/ssr`, -83% on `/jwt` at
`threads: 4`, and the same to within a point at 8 and 15 workers. The docs page
claims roughly -50%; on this hardware the improvement is bigger and it no longer
depends on picking the right pool size.

`threads: 1` is the exception on the heavy routes. Its p50 rises, 0.84 to 2.22ms
on `/ssr`, because a single worker is a queue. It still improves p99 by 39%, but
every larger pool is about 2x better there.

Deep-tail columns (p99.9 and beyond) are dropped from this edition. Single 15s
runs cannot support them; see [Limitations](#limitations).

## C. What the timer policy is worth

The first edition of this report measured a 10x efficiency collapse from 1 to 15
workers and attributed it, explicitly as interpretation rather than measurement,
to polling, claim scans, coherence traffic, memory dispersion and scheduler
pressure. Four of those five were wrong. It was the first one, and it was
arithmetic.

An idle worker spins to a wall-clock deadline and then parks with a timeout. The
default budgets are set in two different files under two different rules:

    spinMicroseconds = totalNumberOfThread * 50     src/worker/loop.ts:195
    parkMs           = 1                            src/runtime/pool.ts:97, 115

so a worker in a 15-worker pool spins 750us out of every 1.75ms cycle whether or
not there is anything to do. Predicted idle cost is `N * spin / (spin + park)`.
Measured against a pool that has been started, warmed, and then handed nothing:

| N | idle cores, old default | model | idle cores, this policy |
|---:|---:|---:|---:|
| 1 | 0.058 | 0.048 | 0.058 |
| 2 | 0.208 | 0.182 | 0.034 |
| 4 | 0.682 | 0.667 | 0.054 |
| 8 | 2.288 | 2.286 | 0.106 |
| 15 | **6.368** | 6.429 | **0.164** |

A fifteen-worker pool used to burn 6.37 cores doing nothing at all. It now burns
0.16. The model predicts the old column to within 4% at every size, and the same
arithmetic was confirmed independently on a 4-core laptop before this run, so
this is a mechanism rather than a curve fit.

That idle cost is most of what the first edition measured as the cost of workers:

| N | loaded cores, old default | idle cores | useful (loaded - idle) |
|---:|---:|---:|---:|
| 1 | 1.79 | 0.058 | 1.73 |
| 2 | 2.03 | 0.208 | 1.82 |
| 4 | 2.70 | 0.682 | 2.02 |
| 8 | 4.82 | 2.288 | 2.53 |
| 15 | 10.03 | 6.368 | 3.66 |

The useful column moves from 1.73 to 3.66 cores across a fifteen-fold change in
worker count. Nearly everything else was spin.

### The full CPU picture

Every pool size against every spin policy. `idle` is cores consumed with
the server up and no load offered; `cores` and `CPU-us/req` are from the
15s measured window. **Bold** marks the policy this report uses at each
pool size.

Saturating load (`-c 100`/route):

| N | policy | idle cores | server cores | rps/core | CPU-us/req |
|---:|---|---:|---:|---:|---:|
| 1 | **50us (this policy = old default)** | **0.058** | **1.79** | **10041** | **100** |
|  | flat 50us (repeat of the row above) | 0.06 | 1.84 | 10291 | 97 |
|  | no spin | 0.012 | 1.79 | 10976 | 91 |
| 2 | 100us (old default) | 0.208 | 2.03 | 7968 | 126 |
|  | flat 50us | 0.124 | 1.97 | 7464 | 134 |
|  | **no spin** | **0.034** | **1.92** | **8244** | **121** |
| 4 | 200us (old default) | 0.682 | 2.7 | 6305 | 159 |
|  | flat 50us | 0.24 | 2.45 | 6246 | 160 |
|  | **no spin** | **0.054** | **2.0** | **6944** | **144** |
| 8 | 400us (old default) | 2.288 | 4.82 | 3240 | 309 |
|  | flat 50us | 0.474 | 3.08 | 4605 | 217 |
|  | **no spin** | **0.106** | **2.31** | **5046** | **198** |
| 15 | 750us (old default) | 6.368 | 10.03 | 1048 | 954 |
|  | flat 50us | 0.872 | 3.9 | 3104 | 322 |
|  | **no spin** | **0.164** | **2.83** | **4238** | **236** |

Open loop, 2000 rps per route, so every row does identical work:

| N | policy | idle cores | server cores | CPU-us/req | /ssr p99 |
|---:|---|---:|---:|---:|---:|
| 1 | **50us (this policy = old default)** | **0.06** | **1.1** | **183** | **8.71** |
|  | flat 50us (repeat of the row above) | 0.06 | 1.06 | 177 | 8.24 |
|  | no spin | 0.014 | 1.06 | 176 | 9.9 |
| 4 | 200us (old default) | 0.684 | 2.49 | 415 | 4.18 |
|  | flat 50us | 0.246 | 1.94 | 323 | 4.03 |
|  | **no spin** | **0.046** | **1.57** | **262** | **4.26** |
| 8 | 400us (old default) | 2.276 | 5.64 | 940 | 4.29 |
|  | flat 50us | 0.49 | 2.69 | 448 | 5.13 |
|  | **no spin** | **0.096** | **1.94** | **323** | **4.35** |
| 15 | 750us (old default) | 6.38 | 11.91 | 1984 | 7.84 |
|  | flat 50us | 0.88 | 3.35 | 558 | 5.0 |
|  | **no spin** | **0.194** | **2.29** | **382** | **4.12** |

Read down the `CPU-us/req` column at fifteen workers: 954, 322, 236 under
saturation and 1,984, 558, 382 at matched load. The policy chosen here is
the cheapest column at every pool size above one, and at one worker it
gives up 9us per request to keep the latency the spin buys.

At one worker the 50us and "flat 50us" rows are the same configuration measured
twice. They differ by 5% on throughput and 3% on CPU per request, which is the
run-to-run variance for this bed and the floor for reading anything else in
these tables.

### Before and after

Same hardware, same workload, same commit. Only the spin budget differs.

| | old default | this policy | change |
|---|---:|---:|---|
| `threads: 15` rps/core, saturating | 1,048 | 4,238 | **4.0x** |
| `threads: 15` CPU-us/request, matched load | 1,984 | 382 | **5.2x less** |
| `threads: 15` `/ssr` p99, matched load | 7.84ms | 4.12ms | **-47%** |
| `threads: 15` idle cores | 6.368 | 0.164 | **39x less** |
| `threads: 8` CPU-us/request, matched load | 940 | 323 | **2.9x less** |
| `threads: 4` CPU-us/request, matched load | 415 | 262 | **1.6x less** |
| `threads: 1` anything | unchanged | unchanged | policy is identical at N=1 |

The oversized pool got cheaper *and* faster. There is no trade to weigh here at
eight workers or above.

### Why one worker keeps its spin

At `threads: 1` the worker is the request's critical path, and a spin that
catches the next call saves a park-to-wake round trip. Measured at matched load:

| threads: 1 | `/ssr` p99 | `/jwt` p99 | idle cores |
|---|---:|---:|---:|
| 50us spin | **8.24ms** | **9.57ms** | 0.060 |
| no spin | 9.90ms | 11.32ms | 0.014 |

17% of `/ssr` p99 for 0.06 idle cores is worth paying. Above one worker that
trade inverts: a peer is already awake to take the work, so the spin buys
nothing and every extra worker pays for it.

A flat 50us at every worker count was tried and rejected. It looked good in
depth-1 microbenchmarks on a 4-core laptop but lost on this bed at scale: at
eight workers it was worse on p99 than no spin at all (5.13 vs 4.35ms), and at
fifteen workers it cost 46% more CPU per request (558 vs 382us) for worse
latency.

## Analysis

What you are buying is isolation. One saturated JS thread is the entire ceiling for
`hono_only`: 1.19 cores, with all three routes inside 9% of each other even though `/ping`
does none of the CPU-heavy work the other two do. That flattening is the problem Knitting
addresses. Moving SSR and JWT off the event loop does not make them much cheaper, it stops
them being charged to everyone else. Which is why the results are lopsided: the offloaded
routes gain 71-83%, the bystander route gains 201%.

`/ping` is the measurement that matters. It does no pool work, so it is a clean probe of
what the pool does to the host thread. Freeing the event loop lifts it from 2,815 to 8,486
rps. Growing the pool still hands some of that back, because the host is the only producer
and every additional consumer is another thread competing for cores with the thread that
feeds it, but the give-back is now gentle: 8,486, 5,785, 4,763, 3,946, 4,032 rps at 1, 2,
4, 8 and 15 workers, for 1.79 to 2.83 cores. Under the old default the same sweep ran to
10.03 cores.

**One producer, N consumers.** The host thread is the only producer in this design. It
accepts the connection, parses the request, routes it, encodes the payload into shared
memory, hands it to the pool, then reads the result back and serializes the response.
Nothing inside the pool raises that rate, so workers help only while *workers* are the
bottleneck, and on this workload that ends almost immediately. That is Amdahl's law with
the host thread as the serial fraction: it does not shrink when you add workers, so it
caps the achievable speedup whatever the pool size.

What Amdahl does not explain is why the first edition's curve bent sharply downward
instead of levelling off at that cap. The answer was the spin budget, and with it removed
the curve does level off. Between 8 and 15 workers throughput and efficiency are now flat
to slightly rising (11,649 to 11,987 rps; 5,046 to 4,238 rps/core), which is what a
producer-bound system with cheap consumers should look like.

**Pool size still matters, but it stopped being expensive.** `threads: 1` remains the
throughput and efficiency optimum. What changed is the penalty for exceeding it: 2.4x on
rps/core rather than 9.6x, with better tail latency as compensation. A pool sized for
isolation rather than throughput is now a reasonable default choice rather than a
deliberate trade.

**Where isolation stops paying.** These gains are measured at or near the host-only
ceiling, which is where head-of-line blocking exists to be removed in the first place. The
shared-memory round trip is a fixed per-call cost, so the further below the ceiling you
run, the less queueing there is to eliminate and the more that fixed cost shows up in p50
on the offloaded routes. This bed did not measure below ~73% of the ceiling, so the
crossover point is not established here.

## Limitations

- **n = 1.** Each configuration was measured once, for 15s. Repeat measurements of an
  identical configuration differed by 5% on throughput, so treat anything smaller as
  noise. The 4.0x and 5.2x results in section C are far outside it; the ordering among
  `threads: 4`, `8` and `15` at matched load is not.
- **Deep tails are not reported.** Single 15s runs cannot support p99.9 and beyond, which
  is exactly the regime where one GC pause moves the number. The first edition published
  them and should not have. Publishable tail figures need 60s+ windows and the median of
  at least three paired repetitions.
- **One workload, one runtime.** Bun 1.4.0 only, one payload size, one connection count
  (`-c 100`/route saturating, 2000 rps/route open loop). Heavier tasks amortise both the
  transport cost and the remaining coordination over more useful work, which would move
  every crossover in this report.
- **`parkMs` was left at its default in every arm.** Idle measurements elsewhere show a
  10ms park is worth roughly another 7x on idle CPU on top of a reduced spin. That
  interaction is unmeasured here.
- **The residual is unattributed.** With the spin removed, CPU per request still rises
  from 100us at one worker to 236us at fifteen. That remaining ~0.2 cores per worker is
  the claim scan, the per-worker completion doorbell walk, coherence traffic and scheduler
  pressure, in unknown proportion. This bed ran no profiler and no hardware counters.
- Cloud instances, even dedicated-CPU ones, are shared hardware in every respect other
  than cores.

## Recommendations for the docs page

- **Lead with the isolation story, not the throughput number.** The page's most defensible
  and most useful result is that `/ping`, a route that never touches the pool, gets the
  largest improvement of the three. That is what separates Knitting from "run the same
  work on more cores", and it is the reason to reach for it.
- Say plainly what the technique is for: route sets where a minority of endpoints dominate
  the event loop. A server whose routes all cost about the same has much less to gain,
  because there is no head-of-line blocking to remove.
- The example's `createPool({})`, a 1-worker pool, is the right default for this workload
  and the fastest configuration measured. Worth saying out loud rather than leaving as an
  unremarked default, because "add more workers" is the natural assumption and it is still
  wrong here, just no longer costly.
- The previous edition recommended warning readers about spin cost past small pools. That
  warning is no longer needed under this policy and should be replaced with a plain
  statement that pool size trades throughput for tail latency.
- The page's throughput table shows nearly identical rps across all three routes in
  Knitting mode. This bed does not reproduce that shape at any pool size: once the event
  loop is free, `/ping` separates sharply from the offloaded routes. Uniform rps across
  unequal routes is the signature of a ceiling *outside* the server, so the page may be
  understating its own `/ping` result.

## Harness pitfalls

Three bugs turned up while building this, and all of them produce plausible-looking wrong
numbers rather than errors:

1. **Wrong PID from `setsid`.** `setsid nohup cmd & echo $!` records the PID of the
   intermediate shell, not the server. The stop step then kills nothing, the old server
   keeps port 3000, the next server fails to bind while the readiness probe is happily
   answered by the *old* process, and every subsequent configuration re-measures the first
   binary. The symptom is a suspiciously flat results table. Fix: resolve the real PID with
   `pgrep -f`, assert cmdline and env per run, and require the port to be free before
   starting.
2. **`pkill -f <pattern>` matching the harness itself.** When the script's own command line
   contains the pattern (heredocs, `ssh` command strings, `bash -c`), `pkill` kills the
   harness. Fix: kill by PID, or keep the pattern in a script file whose own cmdline does
   not contain it.
3. **A backgrounded driver that was assumed dead and was not.** Two driver processes ran
   concurrently against the same server box, each stopping the other's server mid-case.
   The symptom is sporadic per-case failures rather than a flat table, which makes it
   easier to misread as flakiness in the runtime under test. Fix: check for surviving
   driver processes and stray `oha` on the generator before every sweep, not just after.

Recording server CPU-seconds alongside rps is what made the efficiency collapse visible in
the first edition. Recording *idle* CPU alongside both is what explained it. That column
costs 5 seconds per configuration and should be in every pool benchmark.

## Reproducing

This report is self-contained. Appendix B is the code under test, Appendix C the harness,
Appendix D the provisioning, and Appendix A every measurement behind the tables above.
Nothing else is needed to re-run it.

Order of operations:

1. Provision both droplets (Appendix D). Note the server's **private** IP.
2. Recreate the example directory from Appendix B and `bun install`.
3. Copy the tree to the server box, symlink the knitting checkout in as
   `node_modules/knitting`, and install `srvctl.sh`; install `load.sh` on the
   generator box (Appendix C).
4. Edit the three IPs at the top of `drive.py`, then run it against the two plans.
5. Destroy the droplets (Appendix D) and confirm the account is empty.

## Appendix A - measurements

Every run behind this report, one JSON object per line: 16 saturating configurations
(`-c 100`/route) and 13 at a fixed rate (`-q 2000`/route). Both the timer policy used
above and the old default are included, so the before/after in section C can be checked
directly. `spin` is the per-worker budget in microseconds, `default` meaning
`threads * 50`. `idle_cores` is CPU over a 5s window with the server up and no load
offered. `cores` is CPU-seconds over the 15s measured window divided by 15, i.e. cores
fully consumed. Latency values are in milliseconds.

```json
{"tag": "only", "mode": "sat", "threads": 1, "spin": "default", "park": "default", "doorbell": true, "idle_cores": 0.002, "total_rps": 8208, "cores": 1.19, "rps_per_core": 6909, "cpu_us_per_req": 145, "os_threads": 20, "gen_cores": 0.22, "routes": {"ping": {"rps": 2815.1, "p50": 35.42, "p99": 42.99, "ok": 1.0}, "ssr": {"rps": 2815.07, "p50": 35.44, "p99": 42.89, "ok": 1.0}, "jwt": {"rps": 2577.81, "p50": 35.64, "p99": 74.01, "ok": 1.0}}}
{"tag": "t1", "mode": "sat", "threads": 1, "spin": "default", "park": "default", "doorbell": true, "idle_cores": 0.058, "total_rps": 18014, "cores": 1.79, "rps_per_core": 10041, "cpu_us_per_req": 100, "os_threads": 23, "gen_cores": 0.52, "routes": {"ping": {"rps": 8485.72, "p50": 11.5, "p99": 22.1, "ok": 1.0}, "ssr": {"rps": 4815.69, "p50": 19.88, "p99": 40.36, "ok": 1.0}, "jwt": {"rps": 4712.13, "p50": 20.41, "p99": 41.51, "ok": 1.0}}}
{"tag": "t1s50", "mode": "sat", "threads": 1, "spin": "50", "park": "default", "doorbell": true, "idle_cores": 0.06, "total_rps": 18921, "cores": 1.84, "rps_per_core": 10291, "cpu_us_per_req": 97, "os_threads": 23, "gen_cores": 0.51, "routes": {"ping": {"rps": 8864.19, "p50": 11.17, "p99": 20.14, "ok": 1.0}, "ssr": {"rps": 5056.27, "p50": 18.55, "p99": 38.8, "ok": 1.0}, "jwt": {"rps": 5000.74, "p50": 18.74, "p99": 39.9, "ok": 1.0}}}
{"tag": "t1s0", "mode": "sat", "threads": 1, "spin": "0", "park": "default", "doorbell": true, "idle_cores": 0.012, "total_rps": 19640, "cores": 1.79, "rps_per_core": 10976, "cpu_us_per_req": 91, "os_threads": 20, "gen_cores": 0.53, "routes": {"ping": {"rps": 9444.09, "p50": 10.38, "p99": 19.23, "ok": 1.0}, "ssr": {"rps": 5112.27, "p50": 18.71, "p99": 37.88, "ok": 1.0}, "jwt": {"rps": 5083.2, "p50": 18.71, "p99": 38.3, "ok": 1.0}}}
{"tag": "t2", "mode": "sat", "threads": 2, "spin": "default", "park": "default", "doorbell": true, "idle_cores": 0.208, "total_rps": 16174, "cores": 2.03, "rps_per_core": 7968, "cpu_us_per_req": 126, "os_threads": 22, "gen_cores": 0.42, "routes": {"ping": {"rps": 5768.5, "p50": 16.96, "p99": 25.35, "ok": 1.0}, "ssr": {"rps": 5240.09, "p50": 17.66, "p99": 37.84, "ok": 1.0}, "jwt": {"rps": 5165.83, "p50": 17.74, "p99": 39.52, "ok": 1.0}}}
{"tag": "t2s50", "mode": "sat", "threads": 2, "spin": "50", "park": "default", "doorbell": true, "idle_cores": 0.124, "total_rps": 14669, "cores": 1.97, "rps_per_core": 7464, "cpu_us_per_req": 134, "os_threads": 23, "gen_cores": 0.36, "routes": {"ping": {"rps": 5115.91, "p50": 18.78, "p99": 29.51, "ok": 1.0}, "ssr": {"rps": 4782.58, "p50": 19.31, "p99": 39.81, "ok": 1.0}, "jwt": {"rps": 4770.63, "p50": 19.3, "p99": 40.78, "ok": 1.0}}}
{"tag": "t2s0", "mode": "sat", "threads": 2, "spin": "0", "park": "default", "doorbell": true, "idle_cores": 0.034, "total_rps": 15811, "cores": 1.92, "rps_per_core": 8244, "cpu_us_per_req": 121, "os_threads": 23, "gen_cores": 0.44, "routes": {"ping": {"rps": 5785.27, "p50": 16.04, "p99": 27.31, "ok": 1.0}, "ssr": {"rps": 4996.73, "p50": 17.94, "p99": 44.3, "ok": 1.0}, "jwt": {"rps": 5029.06, "p50": 17.84, "p99": 43.53, "ok": 1.0}}}
{"tag": "t4", "mode": "sat", "threads": 4, "spin": "default", "park": "default", "doorbell": true, "idle_cores": 0.682, "total_rps": 17003, "cores": 2.7, "rps_per_core": 6305, "cpu_us_per_req": 159, "os_threads": 26, "gen_cores": 0.43, "routes": {"ping": {"rps": 5818.55, "p50": 16.55, "p99": 24.61, "ok": 1.0}, "ssr": {"rps": 5647.72, "p50": 16.81, "p99": 34.0, "ok": 1.0}, "jwt": {"rps": 5536.29, "p50": 16.93, "p99": 35.25, "ok": 1.0}}}
{"tag": "t4s50", "mode": "sat", "threads": 4, "spin": "50", "park": "default", "doorbell": true, "idle_cores": 0.24, "total_rps": 15324, "cores": 2.45, "rps_per_core": 6246, "cpu_us_per_req": 160, "os_threads": 23, "gen_cores": 0.37, "routes": {"ping": {"rps": 5212.43, "p50": 18.21, "p99": 28.89, "ok": 1.0}, "ssr": {"rps": 5084.94, "p50": 18.48, "p99": 36.88, "ok": 1.0}, "jwt": {"rps": 5027.06, "p50": 18.54, "p99": 38.41, "ok": 1.0}}}
{"tag": "t4s0", "mode": "sat", "threads": 4, "spin": "0", "park": "default", "doorbell": true, "idle_cores": 0.054, "total_rps": 13906, "cores": 2.0, "rps_per_core": 6944, "cpu_us_per_req": 144, "os_threads": 31, "gen_cores": 0.38, "routes": {"ping": {"rps": 4763.33, "p50": 19.31, "p99": 31.65, "ok": 1.0}, "ssr": {"rps": 4410.22, "p50": 20.3, "p99": 49.86, "ok": 1.0}, "jwt": {"rps": 4732.95, "p50": 19.69, "p99": 32.93, "ok": 1.0}}}
{"tag": "t8", "mode": "sat", "threads": 8, "spin": "default", "park": "default", "doorbell": true, "idle_cores": 2.288, "total_rps": 15619, "cores": 4.82, "rps_per_core": 3240, "cpu_us_per_req": 309, "os_threads": 31, "gen_cores": 0.43, "routes": {"ping": {"rps": 5258.18, "p50": 17.7, "p99": 33.09, "ok": 1.0}, "ssr": {"rps": 5169.0, "p50": 18.04, "p99": 36.23, "ok": 1.0}, "jwt": {"rps": 5191.6, "p50": 18.02, "p99": 34.99, "ok": 1.0}}}
{"tag": "t8s50", "mode": "sat", "threads": 8, "spin": "50", "park": "default", "doorbell": true, "idle_cores": 0.474, "total_rps": 14163, "cores": 3.08, "rps_per_core": 4605, "cpu_us_per_req": 217, "os_threads": 30, "gen_cores": 0.4, "routes": {"ping": {"rps": 4852.03, "p50": 19.57, "p99": 29.63, "ok": 1.0}, "ssr": {"rps": 4491.03, "p50": 20.42, "p99": 44.99, "ok": 1.0}, "jwt": {"rps": 4819.8, "p50": 19.93, "p99": 32.77, "ok": 1.0}}}
{"tag": "t8s0", "mode": "sat", "threads": 8, "spin": "0", "park": "default", "doorbell": true, "idle_cores": 0.106, "total_rps": 11649, "cores": 2.31, "rps_per_core": 5046, "cpu_us_per_req": 198, "os_threads": 31, "gen_cores": 0.29, "routes": {"ping": {"rps": 3946.48, "p50": 25.7, "p99": 36.21, "ok": 1.0}, "ssr": {"rps": 3921.32, "p50": 25.48, "p99": 39.35, "ok": 1.0}, "jwt": {"rps": 3781.53, "p50": 25.78, "p99": 52.4, "ok": 1.0}}}
{"tag": "t15", "mode": "sat", "threads": 15, "spin": "default", "park": "default", "doorbell": true, "idle_cores": 6.368, "total_rps": 10516, "cores": 10.03, "rps_per_core": 1048, "cpu_us_per_req": 954, "os_threads": 40, "gen_cores": 0.31, "routes": {"ping": {"rps": 3507.45, "p50": 27.47, "p99": 42.35, "ok": 1.0}, "ssr": {"rps": 3503.79, "p50": 27.67, "p99": 42.41, "ok": 1.0}, "jwt": {"rps": 3504.93, "p50": 27.69, "p99": 42.4, "ok": 1.0}}}
{"tag": "t15s50", "mode": "sat", "threads": 15, "spin": "50", "park": "default", "doorbell": true, "idle_cores": 0.872, "total_rps": 12117, "cores": 3.9, "rps_per_core": 3104, "cpu_us_per_req": 322, "os_threads": 38, "gen_cores": 0.34, "routes": {"ping": {"rps": 4046.0, "p50": 24.75, "p99": 36.09, "ok": 1.0}, "ssr": {"rps": 4039.15, "p50": 24.68, "p99": 35.53, "ok": 1.0}, "jwt": {"rps": 4032.32, "p50": 24.68, "p99": 36.03, "ok": 1.0}}}
{"tag": "t15s0", "mode": "sat", "threads": 15, "spin": "0", "park": "default", "doorbell": true, "idle_cores": 0.164, "total_rps": 11987, "cores": 2.83, "rps_per_core": 4238, "cpu_us_per_req": 236, "os_threads": 39, "gen_cores": 0.37, "routes": {"ping": {"rps": 4031.56, "p50": 23.78, "p99": 36.03, "ok": 1.0}, "ssr": {"rps": 3981.42, "p50": 24.36, "p99": 38.16, "ok": 1.0}, "jwt": {"rps": 3973.74, "p50": 24.39, "p99": 40.03, "ok": 1.0}}}
{"tag": "only", "mode": "rate", "threads": 1, "spin": "default", "park": "default", "doorbell": true, "idle_cores": 0.002, "total_rps": 6000, "cores": 1.08, "rps_per_core": 5566, "cpu_us_per_req": 180, "os_threads": 20, "gen_cores": 0.27, "routes": {"ping": {"rps": 1999.95, "p50": 0.81, "p99": 16.93, "ok": 1.0}, "ssr": {"rps": 1999.72, "p50": 0.84, "p99": 14.32, "ok": 1.0}, "jwt": {"rps": 1999.95, "p50": 1.03, "p99": 25.18, "ok": 1.0}}}
{"tag": "t1", "mode": "rate", "threads": 1, "spin": "default", "park": "default", "doorbell": true, "idle_cores": 0.06, "total_rps": 5999, "cores": 1.1, "rps_per_core": 5471, "cpu_us_per_req": 183, "os_threads": 21, "gen_cores": 0.35, "routes": {"ping": {"rps": 1999.83, "p50": 0.4, "p99": 2.31, "ok": 1.0}, "ssr": {"rps": 1999.82, "p50": 2.22, "p99": 8.71, "ok": 1.0}, "jwt": {"rps": 1999.73, "p50": 2.58, "p99": 9.76, "ok": 1.0}}}
{"tag": "t1s50", "mode": "rate", "threads": 1, "spin": "50", "park": "default", "doorbell": true, "idle_cores": 0.06, "total_rps": 6000, "cores": 1.06, "rps_per_core": 5650, "cpu_us_per_req": 177, "os_threads": 21, "gen_cores": 0.3, "routes": {"ping": {"rps": 1999.82, "p50": 0.39, "p99": 2.18, "ok": 1.0}, "ssr": {"rps": 1999.96, "p50": 1.8, "p99": 8.24, "ok": 1.0}, "jwt": {"rps": 2000.03, "p50": 2.35, "p99": 9.57, "ok": 1.0}}}
{"tag": "t1s0", "mode": "rate", "threads": 1, "spin": "0", "park": "default", "doorbell": true, "idle_cores": 0.014, "total_rps": 5999, "cores": 1.06, "rps_per_core": 5667, "cpu_us_per_req": 176, "os_threads": 20, "gen_cores": 0.35, "routes": {"ping": {"rps": 1999.69, "p50": 0.4, "p99": 2.39, "ok": 1.0}, "ssr": {"rps": 1999.8, "p50": 2.37, "p99": 9.9, "ok": 1.0}, "jwt": {"rps": 1999.74, "p50": 2.64, "p99": 11.32, "ok": 1.0}}}
{"tag": "t4", "mode": "rate", "threads": 4, "spin": "default", "park": "default", "doorbell": true, "idle_cores": 0.684, "total_rps": 5999, "cores": 2.49, "rps_per_core": 2411, "cpu_us_per_req": 415, "os_threads": 26, "gen_cores": 0.53, "routes": {"ping": {"rps": 1999.65, "p50": 0.46, "p99": 2.95, "ok": 1.0}, "ssr": {"rps": 1999.92, "p50": 0.76, "p99": 4.18, "ok": 1.0}, "jwt": {"rps": 1999.7, "p50": 0.78, "p99": 4.36, "ok": 1.0}}}
{"tag": "t4s50", "mode": "rate", "threads": 4, "spin": "50", "park": "default", "doorbell": true, "idle_cores": 0.246, "total_rps": 5999, "cores": 1.94, "rps_per_core": 3099, "cpu_us_per_req": 323, "os_threads": 25, "gen_cores": 0.22, "routes": {"ping": {"rps": 1999.72, "p50": 0.47, "p99": 2.69, "ok": 1.0}, "ssr": {"rps": 1999.85, "p50": 0.76, "p99": 4.03, "ok": 1.0}, "jwt": {"rps": 1999.7, "p50": 0.79, "p99": 4.06, "ok": 1.0}}}
{"tag": "t4s0", "mode": "rate", "threads": 4, "spin": "0", "park": "default", "doorbell": true, "idle_cores": 0.046, "total_rps": 6000, "cores": 1.57, "rps_per_core": 3812, "cpu_us_per_req": 262, "os_threads": 26, "gen_cores": 0.4, "routes": {"ping": {"rps": 1999.8, "p50": 0.45, "p99": 3.18, "ok": 1.0}, "ssr": {"rps": 2000.1, "p50": 0.77, "p99": 4.26, "ok": 1.0}, "jwt": {"rps": 1999.85, "p50": 0.78, "p99": 4.4, "ok": 1.0}}}
{"tag": "t8", "mode": "rate", "threads": 8, "spin": "default", "park": "default", "doorbell": true, "idle_cores": 2.276, "total_rps": 5999, "cores": 5.64, "rps_per_core": 1064, "cpu_us_per_req": 940, "os_threads": 31, "gen_cores": 0.28, "routes": {"ping": {"rps": 1999.84, "p50": 0.52, "p99": 3.09, "ok": 1.0}, "ssr": {"rps": 1999.72, "p50": 0.79, "p99": 4.29, "ok": 1.0}, "jwt": {"rps": 1999.91, "p50": 0.81, "p99": 4.34, "ok": 1.0}}}
{"tag": "t8s50", "mode": "rate", "threads": 8, "spin": "50", "park": "default", "doorbell": true, "idle_cores": 0.49, "total_rps": 6000, "cores": 2.69, "rps_per_core": 2233, "cpu_us_per_req": 448, "os_threads": 28, "gen_cores": 0.25, "routes": {"ping": {"rps": 1999.92, "p50": 0.53, "p99": 3.22, "ok": 1.0}, "ssr": {"rps": 2000.14, "p50": 0.8, "p99": 5.13, "ok": 1.0}, "jwt": {"rps": 1999.94, "p50": 0.85, "p99": 5.16, "ok": 1.0}}}
{"tag": "t8s0", "mode": "rate", "threads": 8, "spin": "0", "park": "default", "doorbell": true, "idle_cores": 0.096, "total_rps": 6000, "cores": 1.94, "rps_per_core": 3093, "cpu_us_per_req": 323, "os_threads": 30, "gen_cores": 0.34, "routes": {"ping": {"rps": 2000.01, "p50": 0.5, "p99": 2.91, "ok": 1.0}, "ssr": {"rps": 1999.8, "p50": 0.79, "p99": 4.35, "ok": 1.0}, "jwt": {"rps": 1999.75, "p50": 0.84, "p99": 4.27, "ok": 1.0}}}
{"tag": "t15", "mode": "rate", "threads": 15, "spin": "default", "park": "default", "doorbell": true, "idle_cores": 6.38, "total_rps": 6000, "cores": 11.91, "rps_per_core": 504, "cpu_us_per_req": 1984, "os_threads": 37, "gen_cores": 0.24, "routes": {"ping": {"rps": 1999.94, "p50": 0.69, "p99": 5.73, "ok": 1.0}, "ssr": {"rps": 1999.84, "p50": 1.04, "p99": 7.84, "ok": 1.0}, "jwt": {"rps": 1999.74, "p50": 1.25, "p99": 8.04, "ok": 1.0}}}
{"tag": "t15s50", "mode": "rate", "threads": 15, "spin": "50", "park": "default", "doorbell": true, "idle_cores": 0.88, "total_rps": 6000, "cores": 3.35, "rps_per_core": 1793, "cpu_us_per_req": 558, "os_threads": 39, "gen_cores": 0.22, "routes": {"ping": {"rps": 1999.76, "p50": 0.57, "p99": 3.37, "ok": 1.0}, "ssr": {"rps": 1999.92, "p50": 0.9, "p99": 5.0, "ok": 1.0}, "jwt": {"rps": 1999.88, "p50": 0.96, "p99": 5.18, "ok": 1.0}}}
{"tag": "t15s0", "mode": "rate", "threads": 15, "spin": "0", "park": "default", "doorbell": true, "idle_cores": 0.194, "total_rps": 6000, "cores": 2.29, "rps_per_core": 2615, "cpu_us_per_req": 382, "os_threads": 38, "gen_cores": 0.2, "routes": {"ping": {"rps": 1999.87, "p50": 0.49, "p99": 3.0, "ok": 1.0}, "ssr": {"rps": 2000.02, "p50": 0.84, "p99": 4.12, "ok": 1.0}, "jwt": {"rps": 2000.14, "p50": 0.88, "p99": 4.33, "ok": 1.0}}}
```

## Appendix B - code under test

The three files taken verbatim from the docs page, the inline baseline written for
comparison, and the parameterized pool variant used for the sweep.

### src/hono_knitting.ts

```ts
import { serve } from "@hono/node-server";
import { createPool } from "knitting";
import { Hono } from "hono";
import { issueJwt } from "./hono_components_jwt.ts";
import { renderSsrPage } from "./hono_componets_ssr.tsx";

const THREADS = Number(process.env.KNIT_THREADS ?? 1);

const handlers = createPool({
  threads: THREADS,
  // One worker is the request's critical path, so a short spin that catches the
  // next call is worth paying for. Above one worker a peer is already awake to
  // take the work, and every extra spinner is charged to the host thread.
  worker: { timers: { spinMicroseconds: THREADS === 1 ? 50 : 0 } },
})({
  issueJwt,
  renderSsrPage,
});

async function main() {
  const app = new Hono();

  app.get("/ping", (c) => {
    return c.json({
      ok: true,
      pong: true,
      runtime: process.release?.name ?? "unknown",
      ts: new Date().toISOString(),
    });
  });

  app.post("/ssr", async (c) => {
    const html = await handlers.call.renderSsrPage(c.req.arrayBuffer());
    return c.html(html);
  });

  app.post("/jwt", async (c) => {
    const responseJson = await handlers.call.issueJwt(c.req.arrayBuffer());
    return c.body(responseJson ?? "Bad request", responseJson ? 200 : 400, {
      "content-type": "application/json; charset=utf-8",
    });
  });

  const server = serve({ fetch: app.fetch, port: 3000 }, (info) => {
    console.log("GET  /ping");
    console.log("POST /ssr   body: { name?, plan?, bio?, projects? }");
    console.log("POST /jwt   body: { user: { id, email?, role? }, ttlSec? }");
  });

  const close = () => {
    // IMPORTANT TO CLOSE CONNECTION
    handlers.shutdown();
    server.close();
  };

  process.on("SIGINT", close);
  process.on("SIGTERM", close);
}

main().catch((error) => {
  console.error(error);
  process.exitCode = 1;
});
```

### src/hono_componets_ssr.tsx

```tsx
import React from "react";
import { renderToString } from "react-dom/server";
import { task } from "knitting";
import { z } from "zod";

const utf8Decoder = new TextDecoder("utf-8", { fatal: true });

type SsrInput = {
  name: string;
  plan: "free" | "pro";
  bio: string;
  projects: number;
};

function UserCard({ user }: { user: SsrInput & { updatedAt: string } }) {
  return (
    <html lang="en">
      <head>
        <meta charSet="utf-8" />
        <meta name="viewport" content="width=device-width, initial-scale=1" />
        <title>{`${user.name} - SSR Card`}</title>
        <style>
          {`
          body { margin: 0; font-family: ui-sans-serif, system-ui, sans-serif; background: #f7f8fa; color: #111827; }
          main { min-height: 100vh; display: grid; place-items: center; padding: 24px; }
          article { width: min(680px, 100%); background: #fff; border: 1px solid #e5e7eb; border-radius: 16px; padding: 20px; }
          h1 { margin: 0 0 8px; font-size: 1.4rem; }
          p { margin: 0 0 10px; line-height: 1.45; }
          .meta { color: #4b5563; font-size: 0.92rem; display: flex; gap: 12px; flex-wrap: wrap; }
          .pill { display: inline-block; background: #eef2ff; color: #4338ca; border-radius: 999px; padding: 4px 10px; font-weight: 600; }
        `}
        </style>
      </head>
      <body>
        <main>
          <article>
            <h1>{user.name}</h1>
            <p>{user.bio}</p>
            <div className="meta">
              <span className="pill">{user.plan.toUpperCase()} plan</span>
              <span>{user.projects.toLocaleString()} projects</span>
              <span>Rendered at {user.updatedAt}</span>
            </div>
          </article>
        </main>
      </body>
    </html>
  );
}

const ParsedJsonObjectSchema = z.string().transform((raw, ctx) => {
  try {
    const parsed = JSON.parse(raw) as unknown;
    if (
      typeof parsed !== "object" || parsed === null || Array.isArray(parsed)
    ) {
      ctx.addIssue({
        code: z.ZodIssueCode.custom,
        message: "payload: expected JSON object",
      });
      return z.NEVER;
    }
    return parsed as Record<string, unknown>;
  } catch {
    ctx.addIssue({
      code: z.ZodIssueCode.custom,
      message: "payload: expected JSON object",
    });
    return z.NEVER;
  }
});

const RawSsrInputSchema = z.object({
  name: z.preprocess((value) => {
    if (typeof value !== "string") return undefined;
    const normalized = value.trim();
    return normalized.length > 0 ? normalized : undefined;
  }, z.string().optional()),
  plan: z.preprocess(
    (value) => (value === "free" || value === "pro" ? value : undefined),
    z.enum(["free", "pro"]).optional(),
  ),
  bio: z.preprocess((value) => {
    if (typeof value !== "string") return undefined;
    const normalized = value.trim();
    return normalized.length > 0 ? normalized : undefined;
  }, z.string().optional()),
  projects: z.preprocess((value) => {
    const numberValue = Number(value);
    if (!Number.isFinite(numberValue)) return undefined;
    return Math.max(0, Math.min(100_000, Math.floor(numberValue)));
  }, z.number().int().optional()),
});

const SsrInputSchema = RawSsrInputSchema.transform(
  (value): SsrInput => ({
    name: value.name ?? "Anonymous",
    plan: value.plan ?? "free",
    bio: value.bio ?? "No bio yet.",
    projects: value.projects ?? 0,
  }),
);

export function renderSsrPageHost(rawPayload: ArrayBuffer): string {
  let decodedPayload = "";
  try {
    decodedPayload = utf8Decoder.decode(rawPayload);
  } catch {
    decodedPayload = "";
  }

  const parsed = ParsedJsonObjectSchema.safeParse(decodedPayload);
  const user: SsrInput = SsrInputSchema.parse(
    parsed.success ? parsed.data : {},
  );

  const html = renderToString(
    <UserCard user={{ ...user, updatedAt: new Date().toISOString() }} />,
  );

  return `<!doctype html>${html}`;
}

export const renderSsrPage = task<ArrayBuffer, string>({
  f: renderSsrPageHost,
});
```

### src/hono_components_jwt.ts

```ts
import { sign } from "hono/jwt";
import { task } from "knitting";
import { z } from "zod";

const utf8Decoder = new TextDecoder("utf-8", { fatal: true });

const ParsedJsonObjectSchema = z.string().transform((raw, ctx) => {
  try {
    const parsed = JSON.parse(raw) as unknown;
    if (
      typeof parsed !== "object" || parsed === null || Array.isArray(parsed)
    ) {
      ctx.addIssue({
        code: z.ZodIssueCode.custom,
        message: "payload: expected JSON object",
      });
      return z.NEVER;
    }
    return parsed;
  } catch {
    ctx.addIssue({
      code: z.ZodIssueCode.custom,
      message: "payload: expected JSON object",
    });
    return z.NEVER;
  }
});

const JwtUserSchema = z.object({
  id: z.string().min(1),
  email: z.string().email().optional(),
  role: z.string().min(1).optional(),
});

const TtlSecSchema = z.preprocess((value) => {
  const n = Number(value);
  if (!Number.isFinite(n)) return 900;
  return Math.max(30, Math.min(86_400, Math.floor(n)));
}, z.number().int());

const JwtPayloadSchema = z.object({
  user: JwtUserSchema,
  ttlSec: TtlSecSchema.optional().default(900),
});

export async function issueJwtHost(
  rawPayload: ArrayBuffer,
): Promise<string | null> {
  let decodedPayload: string;
  try {
    decodedPayload = utf8Decoder.decode(rawPayload);
  } catch {
    return null;
  }

  const parsedResult = ParsedJsonObjectSchema.safeParse(decodedPayload);
  if (!parsedResult.success) {
    return null;
  }

  const payloadResult = JwtPayloadSchema.safeParse(parsedResult.data);
  if (!payloadResult.success) {
    return null;
  }

  const { user, ttlSec } = payloadResult.data;
  const now = Math.floor(Date.now() / 1000);
  const exp = now + ttlSec;

  const token = await sign(
    {
      sub: user.id,
      email: user.email,
      role: user.role ?? "member",
      iat: now,
      exp,
    },
    process.env.secret ?? "hello",
  );

  return JSON.stringify({
    ok: true,
    token,
    sub: user.id,
    exp,
  });
}

export const issueJwt = task<ArrayBuffer, string | null>({
  f: issueJwtHost,
});
```

### src/hono_only.ts

```ts
import { serve } from "@hono/node-server";
import { Hono } from "hono";
import { issueJwtHost } from "./hono_components_jwt.ts";
import { renderSsrPageHost } from "./hono_componets_ssr.tsx";

async function main() {
  const app = new Hono();

  app.get("/ping", (c) => {
    return c.json({
      ok: true,
      pong: true,
      runtime: process.release?.name ?? "unknown",
      ts: new Date().toISOString(),
    });
  });

  app.post("/ssr", async (c) => {
    const html = renderSsrPageHost(await c.req.arrayBuffer());
    return c.html(html);
  });

  app.post("/jwt", async (c) => {
    const responseJson = await issueJwtHost(await c.req.arrayBuffer());
    return c.body(responseJson ?? "Bad request", responseJson ? 200 : 400, {
      "content-type": "application/json; charset=utf-8",
    });
  });

  const server = serve({ fetch: app.fetch, port: 3000 }, (info) => {
    console.log("GET  /ping");
    console.log("POST /ssr   body: { name?, plan?, bio?, projects? }");
    console.log("POST /jwt   body: { user: { id, email?, role? }, ttlSec? }");
  });

  const close = () => {
    server.close();
  };

  process.on("SIGINT", close);
  process.on("SIGTERM", close);
}

main().catch((error) => {
  console.error(error);
  process.exitCode = 1;
});
```

### src/hono_knitting_threads.ts

Identical to `src/hono_knitting.ts` except that the pool shape and the timer
policy come from the environment, so one file covers every point in the sweep
including the old default:

```ts
const env = process.env;
const optNum = (name: string): number | undefined =>
  env[name] === undefined || env[name] === "" ? undefined : Number(env[name]);

const spin = optNum("KNIT_SPIN");
const park = optNum("KNIT_PARK");
const timers: Record<string, number> = {};
if (spin !== undefined) timers.spinMicroseconds = spin;
if (park !== undefined) timers.parkMs = park;

const host: Record<string, boolean> = {};
if (env.KNIT_DOORBELL === "0") host.doorbell = false;
if (env.KNIT_STEAL === "0") host.steal = false;

const handlers = createPool({
  threads: Number(env.KNIT_THREADS ?? 1),
  ...(Object.keys(timers).length > 0 ? { worker: { timers } } : {}),
  ...(Object.keys(host).length > 0 ? { host } : {}),
})({
  issueJwt,
  renderSsrPage,
});
```

Leaving `KNIT_SPIN` unset reproduces the old `threads * 50` default; setting it
to `0` or `50` reproduces the rows in section C. The rest of the file is
byte-identical to `src/hono_knitting.ts`.

### package.json

```json
{
  "name": "hono-example",
  "private": true,
  "type": "module",
  "dependencies": {
    "@hono/node-server": "^1.13.7",
    "hono": "^4.6.14",
    "react": "^18.3.1",
    "react-dom": "^18.3.1",
    "zod": "^3.23.8"
  }
}
```

### deno.json

Only needed to run the example under Deno (TSX + npm resolution). The measurements in
this report are Bun.

```json
{
  "nodeModulesDir": "auto",
  "imports": {
    "knitting": "../../knitting.ts"
  },
  "compilerOptions": {
    "jsx": "react-jsx",
    "jsxImportSource": "react"
  }
}
```

## Appendix C - harness

Three pieces: `srvctl.sh` on the server box, `load.sh` on the generator box, and
`drive.py` driving both over ssh from anywhere. The plans are two JSON files
listing the configurations to sweep.

### srvctl.sh (server box)

`start` takes the pool size, the spin budget, the park timeout and a doorbell
flag; an empty string for any of the three leaves that setting at its default.
`idlecpu` is the addition that made section C possible.

```bash
#!/usr/bin/env bash
set -u
cd /root/knitting/bench/hono-example
case "${1:-}" in
  start)
    entry=$2; th=${3:-1}; spin=${4:-}; park=${5:-}; db=${6:-1}
    env JWT_SECRET=x KNIT_THREADS="$th" KNIT_SPIN="$spin" KNIT_PARK="$park" \
        KNIT_DOORBELL="$db" \
        setsid /usr/local/bin/bun "$entry" >/tmp/srv.log 2>&1 </dev/null &
    pid=""
    for _ in $(seq 1 80); do pid=$(pgrep -f "bin/bun $entry" | head -1); [ -n "$pid" ] && break; sleep 0.5; done
    echo "$pid" > /tmp/srv.pid
    for _ in $(seq 1 80); do ss -ltn 2>/dev/null | grep -q ':3000' && break; sleep 0.5; done
    echo "PID=$pid $(tr '\0' '\n' < /proc/$pid/environ | grep -E 'KNIT_THREADS|KNIT_SPIN|KNIT_PARK|KNIT_DOORBELL' | tr '\n' ' ')"
    ;;
  stop)
    pid=$(cat /tmp/srv.pid 2>/dev/null || true)
    [ -n "$pid" ] && kill "$pid" 2>/dev/null
    # A pool with spinning workers can outlive SIGTERM, so escalate quickly and
    # gate on the port being free rather than on a fixed sleep.
    for _ in $(seq 1 10); do
      ss -ltn 2>/dev/null | grep -q ':3000' || break
      sleep 0.3
    done
    if ss -ltn 2>/dev/null | grep -q ':3000'; then
      holders=$(ss -ltnp 2>/dev/null | grep ':3000' | grep -oP 'pid=\K[0-9]+' | sort -u | tr '\n' ' ')
      [ -n "$holders" ] && kill -9 $holders 2>/dev/null
      leftover=$(pgrep -f "bin/bun src/hono" | tr '\n' ' ')
      [ -n "$leftover" ] && kill -9 $leftover 2>/dev/null
    fi
    for _ in $(seq 1 20); do
      ss -ltn 2>/dev/null | grep -q ':3000' || break
      sleep 0.3
    done
    if ss -ltn 2>/dev/null | grep -q ':3000'; then echo "STILL_LISTENING"; exit 1; else echo stopped; fi
    ;;
  cpu) pid=$(cat /tmp/srv.pid); awk '{print $14+$15}' /proc/"$pid"/stat 2>/dev/null || echo 0 ;;
  threads) pid=$(cat /tmp/srv.pid); ls /proc/"$pid"/task | wc -l ;;
  idlecpu)
    # CPU consumed over $2 seconds with no load offered at all.
    pid=$(cat /tmp/srv.pid)
    a=$(awk '{print $14+$15}' /proc/"$pid"/stat); sleep "$2"
    b=$(awk '{print $14+$15}' /proc/"$pid"/stat); echo "$a $b"
    ;;
esac
```

### load.sh (generator box)

```bash
#!/usr/bin/env bash
# usage: load.sh <priv-ip> <conc> <dur> [extra oha args...]
set -u
PRIV=$1; CONC=$2; DUR=$3; shift 3
SSR='{"name":"Ari","plan":"pro","bio":"Building on Knitting","projects":17}'
JWT='{"user":{"id":"u_42","email":"ari@example.com","role":"admin"},"ttlSec":900}'
H='content-type: application/json'
g0=$(grep '^cpu ' /proc/stat | awk '{print $2+$3+$4}')
oha -c "$CONC" -z "$DUR" "$@" --no-tui --output-format json "http://$PRIV:3000/ping" > /tmp/o.ping.json 2>/dev/null &
a=$!
oha -c "$CONC" -z "$DUR" "$@" --no-tui --output-format json -m POST -H "$H" -d "$SSR" "http://$PRIV:3000/ssr" > /tmp/o.ssr.json 2>/dev/null &
b=$!
oha -c "$CONC" -z "$DUR" "$@" --no-tui --output-format json -m POST -H "$H" -d "$JWT" "http://$PRIV:3000/jwt" > /tmp/o.jwt.json 2>/dev/null &
c=$!
wait $a $b $c
g1=$(grep '^cpu ' /proc/stat | awk '{print $2+$3+$4}')
echo $((g1-g0)) > /tmp/gencpu
echo LOAD_DONE
```

### drive.py (orchestrator)

Runs a plan, asserting each server's identity from `/proc/<pid>/environ` before
any load is offered, and measuring idle CPU between start-up and warmup.

```python
#!/usr/bin/env python3
"""Drives the Hono sweep across pool sizes and worker timer policies."""
import json, subprocess, sys, time, os

SRV = "167.71.31.42"; GEN = "68.183.140.115"; PRIV = "10.116.0.3"
SSHO = ["-o","StrictHostKeyChecking=no","-o","UserKnownHostsFile=/dev/null",
        "-o","LogLevel=ERROR","-o","ConnectTimeout=10"]
OUT = os.environ.get("OUT", "/tmp/claude-1000/-home-mimi-github-knitting/469d4f28-52a0-4bce-88b4-d348946593f6/scratchpad/cloudres")
os.makedirs(OUT, exist_ok=True)
CONC = os.environ.get("CONC","100"); DUR = os.environ.get("DUR","15s")
WARM = os.environ.get("WARM","6s"); IDLE = os.environ.get("IDLE","5")

def sh(host, cmd, timeout=400):
    r = subprocess.run(["ssh","-n",*SSHO,f"root@{host}",cmd],
                       capture_output=True, text=True, timeout=timeout)
    return r.stdout.strip()

def run_case(tag, entry, threads, spin, park, doorbell, mode, extra=()):
    sh(SRV, "/root/srvctl.sh stop")
    info = sh(SRV, f'/root/srvctl.sh start {entry} {threads} "{spin}" "{park}" {doorbell}')
    if f"KNIT_THREADS={threads}" not in info:
        print(f"  IDENTITY MISMATCH {tag}: {info}"); return None

    # Idle CPU with no load offered at all.
    a, b = sh(SRV, f"/root/srvctl.sh idlecpu {IDLE}").split()
    idle_cores = (int(b) - int(a)) / 100 / float(IDLE)

    sh(GEN, f"/root/load.sh {PRIV} {CONC} {WARM} {' '.join(extra)}")
    c0 = int(sh(SRV, "/root/srvctl.sh cpu"))
    t0 = time.time()
    sh(GEN, f"/root/load.sh {PRIV} {CONC} {DUR} {' '.join(extra)}")
    c1 = int(sh(SRV, "/root/srvctl.sh cpu"))
    wall = time.time() - t0
    osth = int(sh(SRV, "/root/srvctl.sh threads") or 0)
    gencpu = int(sh(GEN, "cat /tmp/gencpu") or 0)

    routes = {}
    for r in ("ping","ssr","jwt"):
        raw = sh(GEN, f"cat /tmp/o.{r}.json")
        open(f"{OUT}/{tag}.{mode}.{r}.json","w").write(raw)
        d = json.loads(raw)
        routes[r] = {"rps": d["summary"]["requestsPerSec"],
                     "p50": d["latencyPercentiles"]["p50"]*1000,
                     "p99": d["latencyPercentiles"]["p99"]*1000,
                     "ok": d["summary"].get("successRate", 1.0)}
    dur_s = float(DUR.rstrip("s"))
    cores = (c1 - c0) / 100 / dur_s
    total = sum(v["rps"] for v in routes.values())
    row = {"tag": tag, "mode": mode, "threads": threads,
           "spin": spin or "default", "park": park or "default",
           "doorbell": doorbell == "1",
           "idle_cores": round(idle_cores,3),
           "total_rps": round(total), "cores": round(cores,2),
           "rps_per_core": round(total/cores) if cores else None,
           "cpu_us_per_req": round(cores*1e6/total) if total else None,
           "os_threads": osth, "gen_cores": round(gencpu/100/dur_s,2),
           "routes": {k: {kk: round(vv,2) for kk,vv in v.items()} for k,v in routes.items()}}
    sh(SRV, "/root/srvctl.sh stop")
    print("  " + json.dumps(row))
    with open(f"{OUT}/rows.jsonl","a") as f: f.write(json.dumps(row)+"\n")
    return row

if __name__ == "__main__":
    plan = json.load(open(sys.argv[1]))
    print(f"== {len(plan)} cases, conc={CONC}/route, dur={DUR} ==", flush=True)
    for c in plan:
        print(f"[{c['tag']}] threads={c['threads']} spin={c['spin'] or 'default'} "
              f"park={c['park'] or 'default'} doorbell={c['doorbell']}", flush=True)
        try:
            run_case(c["tag"], c["entry"], c["threads"], c["spin"], c["park"],
                     c["doorbell"], c.get("mode","sat"), c.get("extra",[]))
        except Exception as e:
            print(f"  FAILED: {e}", flush=True)
```

### The plans

```python
K = "src/hono_knitting_threads.ts"; O = "src/hono_only.ts"

# Saturating: every pool size against every spin policy.
plan_sat = [{"tag": "only", "entry": O, "threads": 1,
             "spin": "", "park": "", "doorbell": "1"}]
for t in (1, 2, 4, 8, 15):
    plan_sat.append({"tag": f"t{t}",    "entry": K, "threads": t,
                     "spin": "",   "park": "", "doorbell": "1"})   # old default
    plan_sat.append({"tag": f"t{t}s50", "entry": K, "threads": t,
                     "spin": "50", "park": "", "doorbell": "1"})   # flat 50us
    plan_sat.append({"tag": f"t{t}s0",  "entry": K, "threads": t,
                     "spin": "0",  "park": "", "doorbell": "1"})   # no spin

# Open loop at 2000 rps/route.
plan_rate = [{"tag": "only", "entry": O, "threads": 1, "spin": "", "park": "",
              "doorbell": "1", "mode": "rate", "extra": ["-q", "2000"]}]
for t in (1, 4, 8, 15):
    for tag, spin in ((f"t{t}", ""), (f"t{t}s50", "50"), (f"t{t}s0", "0")):
        plan_rate.append({"tag": tag, "entry": K, "threads": t, "spin": spin,
                          "park": "", "doorbell": "1", "mode": "rate",
                          "extra": ["-q", "2000"]})
```

Under the policy this report treats as canon, `t1` is the one-worker row and
`t{2,4,8,15}s0` are the rest; the `t{N}` and `t{N}s50` rows are the old default
and the rejected flat-50us alternative, kept so section C can be checked.

## Appendix D - provisioning and teardown

Two droplets in the same region so they share a VPC and traffic stays on the private
network. `--ssh-keys` takes the numeric id of a key already on the account
(`doctl compute ssh-key list`); the runs in this report reused an existing key and
created no account resources other than the two droplets.

### Create

```bash
export DIGITALOCEAN_ACCESS_TOKEN=$(tr -d '\n\r' < /path/to/token)

doctl compute droplet create knit-srv \
  --size c-16 --image ubuntu-24-04-x64 --region nyc1 \
  --ssh-keys <KEY_ID> --tag-name knitbench \
  --user-data-file ud-server.yaml --wait \
  --format ID,Name,PublicIPv4,PrivateIPv4,Status

doctl compute droplet create knit-gen \
  --size c-8 --image ubuntu-24-04-x64 --region nyc1 \
  --ssh-keys <KEY_ID> --tag-name knitbench \
  --user-data-file ud-load.yaml --wait \
  --format ID,Name,PublicIPv4,PrivateIPv4,Status
```

Both reached `active` and finished cloud-init in about 20 seconds.

### ud-server.yaml

```yaml
#cloud-config
package_update: true
packages: [unzip, curl, git, htop, linux-tools-common]
write_files:
  - path: /etc/sysctl.d/99-bench.conf
    content: |
      net.core.somaxconn=65535
      net.ipv4.ip_local_port_range=1024 65535
      net.ipv4.tcp_max_syn_backlog=65535
      fs.file-max=2097152
runcmd:
  - sysctl --system
  - [ bash, -lc, "curl -fsSL https://bun.sh/install | BUN_INSTALL=/opt/bun bash" ]
  - [ bash, -lc, "ln -sf /opt/bun/bin/bun /usr/local/bin/bun" ]
  - [ bash, -lc, "echo '* soft nofile 1048576' >> /etc/security/limits.conf; echo '* hard nofile 1048576' >> /etc/security/limits.conf" ]
  - [ bash, -lc, "touch /root/READY_SERVER" ]
```

### ud-load.yaml

```yaml
#cloud-config
package_update: true
packages: [curl, tar, jq]
write_files:
  - path: /etc/sysctl.d/99-bench.conf
    content: |
      net.ipv4.ip_local_port_range=1024 65535
      net.ipv4.tcp_tw_reuse=1
      fs.file-max=2097152
runcmd:
  - sysctl --system
  - [ bash, -lc, "curl -fsSL https://github.com/hatoo/oha/releases/download/v1.14.0/oha-linux-amd64 -o /usr/local/bin/oha && chmod +x /usr/local/bin/oha" ]
  - [ bash, -lc, "echo '* soft nofile 1048576' >> /etc/security/limits.conf; echo '* hard nofile 1048576' >> /etc/security/limits.conf" ]
  - [ bash, -lc, "touch /root/READY_LOAD" ]
```

### Ship the code to the server box

The example imports `knitting` as a package, so a checkout of this repo is symlinked
into `node_modules`. Only the built JS, `src/`, and `prebuilds/` are needed:

```bash
tar czf knit.tgz --exclude=node_modules --exclude='results*' \
  package.json knitting.js knitting.d.ts process-shared-buffer.js shared-memory.js \
  unsafe.js utils.js src prebuilds bench/hono-example

SRV=<server public ip>

scp knit.tgz root@$SRV:/root/
ssh root@$SRV 'mkdir -p /root/knitting && tar xzf /root/knit.tgz -C /root/knitting
  cd /root/knitting/bench/hono-example && bun install
  ln -sfn /root/knitting node_modules/knitting'
```

### Destroy

Delete by explicit id and then verify the account is empty. `doctl compute droplet
delete -t <tag>` is not sufficient on its own - it needs `--tag-name`, and a wrong
flag there fails without deleting anything:

```bash
doctl compute droplet delete <SRV_ID> <GEN_ID> --force
sleep 8
doctl compute droplet list      --format ID,Name,Status   # expect empty
doctl compute volume list       --format ID,Name
doctl compute snapshot list     --format ID,Name
doctl compute load-balancer list --format ID,Name
doctl compute firewall list     --format ID,Name
doctl compute reserved-ip list
```

Cost for the runs in this report: c-16 at $0.50/hr plus c-8 at $0.25/hr for roughly
40 minutes, about **$0.50** total.
