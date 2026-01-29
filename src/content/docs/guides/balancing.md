---
title: Balancing strategies
description: Control how tasks are routed to workers.
sidebar:
  order: 7
---

You can choose how calls are routed across worker lanes with the `balancer`
option:

- `"robinRound"` default round-robin
- `"firstIdle"` prefer idle workers
- `"randomLane"` choose a random worker
- `"firstIdleOrRandom"` idle first, then random

```ts
const pool = createPool({
  threads: 4,
  balancer: "firstIdle",
})({ add });
```
