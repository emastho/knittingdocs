---
title: Creating pools
description: Spin up workers and call tasks.
sidebar:
  order: 5
---

`createPool(options)(tasks)` starts worker threads and returns helpers:

- `call.<task>(args)` enqueue a task and return a promise.
- `fastCall.<task>(args)` enqueue via the fast path (same signature).
- `send()` flush the batch to workers.
- `shutdown()` stop all workers.

`call.*()` always returns a promise. Inputs may also be promises; they are
resolved on the host before dispatch.

## Example

```ts
import { createPool, isMain, task } from "@vixeny/knitting";

export const add = task<[number, number], number>({
  f: async ([a, b]) => a + b,
});

const { call, send, shutdown } = createPool({
  threads: 2,
})({ add });

if (isMain) {
  const jobs = [call.add([1, 2]), call.add([3, 4])];
  send();
  const results = await Promise.all(jobs);
  console.log(results);
  shutdown();
}
```
