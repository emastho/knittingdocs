---
title: Custom worker entry
description: Override the worker entry module with source.
sidebar:
  order: 11
---

By default, knitting uses its own worker entry. If you want a custom entry
(module initialization, extra globals, etc.), pass `source` to `createPool`.

```ts
const pool = createPool({
  threads: 2,
  source: new URL("./my-worker.ts", import.meta.url).href,
})({ add });
```

In your worker entry, import `workerMainLoop`. The module starts the loop when
it detects a worker thread, or you can call it explicitly:

```ts
import { workerMainLoop } from "@vixeny/knitting";
import { workerData } from "node:worker_threads";

workerMainLoop(workerData as any);
```
