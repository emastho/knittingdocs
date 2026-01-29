---
title: Timeouts
description: Use default values when work is slow.
sidebar:
  order: 4
---

```ts
import { createPool, isMain, task } from "@vixeny/knitting";

export const slow = task<string, string>({
  timeout: { time: 50, default: "fallback" },
  f: async (value) => {
    await new Promise((r) => setTimeout(r, 200));
    return value;
  },
});

const { call, shutdown } = createPool({ threads: 1 })({ slow });

if (isMain) {
  const result = await call.slow("hello");
  console.log(result); // "fallback"
  shutdown();
}
```
