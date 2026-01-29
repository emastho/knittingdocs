---
title: Hello world
description: The smallest working pool.
sidebar:
  order: 1
---

```ts
import { createPool, isMain, task } from "@vixeny/knitting";

export const hello = task({
  f: async () => "hello",
});

const { call, shutdown } = createPool({ threads: 1 })({ hello });

if (isMain) {
  const result = await call.hello();
  console.log(result);
  shutdown();
}
```
