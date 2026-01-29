---
title: Task timeouts
description: Timeout shapes and behavior.
sidebar:
  order: 3
---

Timeouts are defined on a task and apply per call.

```ts
task({ timeout: 100, f })
```

Supported forms:

- `number` (ms). Non-negative values reject with `Error("Task timeout")`.
- `{ time: number, default: value }` resolves with the provided value.
- `{ time: number, maybe: true }` resolves with `undefined`.
- `{ time: number, error: value }` rejects with the provided error.

If `time` is negative or missing, timeouts are ignored.
