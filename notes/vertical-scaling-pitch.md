# Pitch exploration: protect the event loop, use the whole box

Status: working note, not docs copy. This is a recommendation for how to frame
Knitting before changing `src/content/docs/extras/why.mdx`.

## The recommendation

Do not sell Knitting as vertical scaling. Sell **performance isolation at
function granularity**.

> Knitting gives CPU-heavy JavaScript functions their own local execution lane,
> so they stop blocking the rest of the application without becoming services.

Multicore utilization is an important economic payoff, but it is not the
product's identity. The developer recognizes the hot-function problem first;
better capacity per replica is the reason fixing it can pay for itself.

The positioning stack is:

1. **Problem:** a few expensive functions monopolize the event loop, so cheap
   work queues behind expensive work.
2. **Product:** a typed, function-level execution boundary onto threads or
   isolated processes.
3. **Immediate outcome:** unrelated work remains responsive under CPU-heavy
   load.
4. **Infrastructure outcome:** a multicore deployment can use compute that one
   serialized event loop cannot productively reach.
5. **Operational outcome:** the code stays in the application, repository, and
   deploy unit instead of becoming a service.

The short version:

> **Keep expensive JavaScript off the event loop, not out of the application.**

## What the current benchmark actually sells

The strongest result is the fixed-rate test, not the saturated total-rps test.
At the same 6,000 requests per second and the same 1:1:1 route mix:

| | server cores | `/ping` p99 | `/ssr` p99 | `/jwt` p99 |
|---|---:|---:|---:|---:|
| `hono_only` | 1.08 | 16.93 ms | 14.32 ms | 25.18 ms |
| `threads: 1` | 1.10 | 2.31 ms | 8.71 ms | 9.76 ms |

`/ping` never touches the pool. For essentially the same CPU cost, its p99
falls by 86% because expensive work no longer owns the event loop. That is
direct evidence for performance isolation:

> The same mixed workload gets dramatically better tail latency because heavy
> work no longer blocks cheap work.

The saturation result is still useful:

| | server cores | total rps | rps/core |
|---|---:|---:|---:|
| `hono_only` | 1.19 | 8,208 | 6,909 |
| `threads: 1` | 1.79 | 18,014 | 10,041 |

It shows that one worker lets the server spend another 0.60 cores and complete
far more work. It does **not yet prove** that the same traffic can run on 30%
fewer boxes.

The three routes are driven by separate closed-loop generators, so the mix of
completed work changes. `/ping`, the cheapest route, grows from about 34% of
completed requests under `hono_only` to about 47% with one worker. Aggregate
RPS across unlike routes is therefore not a clean unit of work, and the
increase in RPS/core is partly the system completing a larger share of cheap
requests.

The honest conclusion is:

- Knitting breaks head-of-line blocking.
- It makes otherwise inaccessible parallel capacity useful.
- It greatly improves tail latency at matched load.
- Fewer boxes at a fixed SLO is plausible, but has not been measured yet.

## The frame

The hot-function story and the capacity story should be one causal narrative,
not two competing sections:

1. **Your event loop can be full while your machine is not.** A handful of
   CPU-heavy functions can saturate the serialized request path while other
   compute remains available.
2. **Move only the work causing the blockage.** Keep the function in the same
   codebase and deploy unit, but give its execution another lane.
3. **Cheap work becomes cheap again.** The main thread remains available for
   coordination, I/O completions, and routes that do little CPU work.
4. **Then scale out the better-shaped replica.** Horizontal scaling is still
   correct; each replica now has workload separation inside it.

This avoids treating horizontal scaling as the enemy. The point is not that
every horizontally scaled JavaScript service wastes a fixed amount of CPU. The
point is that adding replicas does not itself create a boundary between cheap
and expensive work.

## What not to lead with

### "You cannot rent 1.2 vCPU"

This is memorable but too fragile to carry the pitch. Cloud packaging varies:
Azure B-series and DigitalOcean Basic include one-vCPU options, while common
AWS T3 and Google E2 shapes expose two vCPUs with different bursting, sharing,
and SMT behavior. Containers can also be assigned fractional CPU limits.

The durable version is:

> **Your event loop can be full while your machine is not.**

That describes the software problem without making the product depend on a
particular provider's SKU catalog.

### "Knitting makes every box 45% more efficient"

The current benchmark does not establish this for a fixed workload. At matched
load, one worker uses essentially the same CPU and delivers much better p99.
That is already a strong result and does not need to be stretched into a cost
claim.

The economic metric should eventually be **fixed-mix throughput at a fixed p99
SLO per dollar**, not unconstrained aggregate RPS/core.

### "Idle CPU is the entire argument"

Idle efficiency keeps the product honest, but it is not the entire argument.
The argument is that one class of work should not block another. The worker
pool must then avoid consuming the capacity it exists to recover.

A docs-level line could be:

> A pool intended to recover spare capacity should consume almost none when it
> has no work.

The 39x reduction in idle CPU is excellent engineering evidence for the
Architecture page and benchmark report. It is too much implementation history
for the main `why.mdx` narrative.

## The competitive story

### Versus running inline

Inline work has no boundary. A CPU-heavy function occupies the event loop and
unrelated requests wait behind it. Knitting creates the boundary at the few
functions that need one.

### Versus hand-rolled workers and worker pools

The category is still a worker/concurrency runtime, so it is too broad to say
that other pools merely sell parallelism while Knitting alone sells
efficiency. The concrete differentiation is more credible:

- an exported function becomes a typed async call;
- shared-memory transport keeps the boundary practical for smaller work;
- the main event loop and heavy work have distinct execution lanes;
- idle workers are deliberately cheap;
- the same call model can use threads or isolated processes.

### Versus two server processes or cluster mode

Two processes are a serious baseline. They can use another core, and a load
balancer can reduce some queueing. The answer cannot just be that cluster mode
copies a bad shape.

The architectural distinction is that cluster mode duplicates the whole
application and gives every process the same mixed workload. Knitting separates
workload classes: the host handles coordination and cheap work while workers
handle selected expensive functions. A cluster can approximate that separation
with route-specific processes and routing, but that is the additional machinery
Knitting is meant to avoid.

The remaining claims need measurement. In particular, the pitch should not
claim lower resident memory or better p99 than two processes until CPU, RSS,
throughput, and latency have been compared directly.

### Versus a service

A service is right when the work needs independent ownership, deployment,
cross-machine scale, or a separate failure domain. It is expensive when one
function merely needs somewhere else to execute. Knitting offers service-like
workload separation without introducing a network and deploy boundary.

## Who this is for

The sharpest initial audience is a Node.js, Bun, or Deno service where:

- a small number of functions account for much of the CPU time;
- cheap and expensive requests currently share an event loop;
- the deployment has meaningful parallel compute available;
- the code belongs to the same team and should remain one deploy unit;
- tail latency or per-replica capacity matters.

It is not primarily for workloads waiting on databases or networks, deployments
strictly limited to one CPU, or functions that already need independent service
ownership.

## The benchmark that would establish the economic claim

Run the small-instance benchmark, but make the question:

> At a fixed, realistic request mix and a fixed p99 SLO, how much traffic can
> one replica serve?

Compare:

1. inline Hono;
2. two Hono processes behind a local load balancer;
3. Hono with one Knitting worker.

Use at least one two-core ARM instance without SMT and one two-vCPU x86 instance
with SMT. Keep request proportions fixed rather than giving each route an
independent closed-loop generator. Record:

- maximum sustained throughput below the p99 target;
- CPU-seconds per fixed unit of work;
- resident memory;
- idle CPU;
- approximate cost per million requests.

That test can support claims such as "more SLO-safe traffic per replica" or
"fewer replicas for the same workload." Until it exists, the pitch should lead
with the result already demonstrated: **performance isolation without a service
boundary**.

## Candidate language

Primary:

> **Keep expensive JavaScript off the event loop, not out of the application.**

Supporting lines:

- "Your event loop can be full while your machine is not."
- "Give heavy functions their own execution lane."
- "Service-like workload separation, without another service."
- "Scale out when you need to. First make each replica a better place to run
  mixed work."

Category sentence:

> Knitting is a function-level execution boundary for JavaScript: typed calls
> run on threads or isolated processes while the application stays responsive
> and remains one deploy unit.
