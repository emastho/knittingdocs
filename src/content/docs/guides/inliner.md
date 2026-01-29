---
title: Inliner lane
description: Run tasks on the main thread as an extra lane.
sidebar:
  order: 8
---

The `inliner` option adds a main-thread execution lane. This can reduce
latency for small tasks or when you want to keep one lane local.

```ts
const pool = createPool({
  threads: 3,
  inliner: { position: "last" },
})({ add });
```

Use `position: "first"` if you want the inliner to be the first lane.
