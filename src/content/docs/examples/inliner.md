---
title: Inliner lane
description: Add a main-thread execution lane.
sidebar:
  order: 3
---

```ts
import { createPool, isMain, task } from "@vixeny/knitting";

export const add = task<[number, number], number>({
  f: async ([a, b]) => a + b,
});

const { call, shutdown } = createPool({
  threads: 2,
  inliner: { position: "last" },
})({ add });

if (isMain) {
  const results = await Promise.all([
    call.add([1, 2]),
    call.add([3, 4]),
  ]);
  console.log(results);
  shutdown();
}
```
