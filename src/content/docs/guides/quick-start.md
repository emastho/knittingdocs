---
title: Quick Start
description: Run your first tasks with a worker pool.
sidebar:
  order: 3
---

```ts
import { createPool, isMain, task } from "@vixeny/knitting";

export const hello = task({
  f: async () => "hello",
});

export const world = task({
  f: async () => "world",
});

const { call, shutdown } = createPool({
  threads: 2,
})({
  hello,
  world,
});

if (isMain) {
  const jobs = [
    call.hello(),
    call.world(),
    call.hello(),
    call.world(),
  ];

  const results = await Promise.all(jobs);
  console.log("Results:", results);
  shutdown();
}
```
