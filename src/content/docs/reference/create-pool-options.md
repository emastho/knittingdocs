---
title: createPool options
description: Full list of pool configuration options.
sidebar:
  order: 2
---

```ts
createPool({
  threads?: number,
  inliner?: { position?: "first" | "last" },
  balancer?: "robinRound" | "firstIdle" | "randomLane" | "firstIdleOrRandom",
  worker?: {
    resolveAfterFinishingAll?: true,
    timers?: {
      spinMicroseconds?: number,
      parkMs?: number,
      pauseNanoseconds?: number,
    },
  },
  dispatcher?: {
    stallFreeLoops?: number,
    maxBackoffMs?: number,
  },
  debug?: {
    extras?: boolean,
    logMain?: boolean,
    logHref?: boolean,
    logImportedUrl?: boolean,
  },
  source?: string,
})
```

Notes:

- `threads` defaults to `1`.
- `inliner` adds a main-thread lane.
- `balancer` selects the routing strategy.
- `worker` and `dispatcher` tune idle behavior and backoff.
- `source` overrides the worker entry module.
