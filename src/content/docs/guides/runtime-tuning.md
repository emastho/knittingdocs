---
title: Runtime tuning
description: Adjust spin and backoff settings for latency vs throughput.
sidebar:
  order: 10
---

You can tune idle behavior and backoff with `worker.timers` and
`dispatcher` options.

## Worker timers

- `spinMicroseconds` busy-spin budget before parking (microseconds)
- `parkMs` `Atomics.wait` timeout when parked (milliseconds)
- `pauseNanoseconds` `Atomics.pause` duration while spinning (nanoseconds)

## Dispatcher

- `stallFreeLoops` number of notify loops before backoff starts
- `maxBackoffMs` maximum backoff delay (milliseconds)

```ts
const pool = createPool({
  threads: 2,
  worker: {
    timers: {
      spinMicroseconds: 40,
      parkMs: 10,
      pauseNanoseconds: 200,
    },
  },
  dispatcher: {
    stallFreeLoops: 64,
    maxBackoffMs: 5,
  },
})({ add });
```
