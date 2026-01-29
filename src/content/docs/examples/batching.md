---
title: Batching calls
description: Enqueue many tasks, then send once.
sidebar:
  order: 2
---

```ts
import { createPool, isMain, task } from "@vixeny/knitting";

export const hello = task({
  f: async () => "hello",
});

const { call, send, shutdown } = createPool({ threads: 2 })({ hello });

if (isMain) {
  const jobs = Array.from({ length: 1_000 }, () => call.hello());
  send();
  const results = await Promise.all(jobs);
  console.log(results.length);
  shutdown();
}
```
