---
title: Overview
description: What knitting is and how it works.
sidebar:
  order: 1
---

Knitting is a shared-memory worker pool for Node.js, Deno, and Bun. You define
small tasks at module scope, export them, and then create a pool that can call
those tasks from the main thread.

## Core ideas

- **Task**: A wrapped function created with `task({ f, ... })`. Tasks include
  metadata used by workers to find and execute the function.
- **Pool**: A set of worker threads plus a dispatcher. `createPool()` returns
  `call`, `fastCall`, `send`, and `shutdown` helpers.
- **Shared memory transport**: Calls are encoded into shared buffers, reducing
  overhead compared to message passing.
- **Batching**: `call.*()` enqueues work, and `send()` can flush a batch to
  reduce wakeups under load.

## Typical flow

1. Define tasks at module scope and export them.
2. Create a pool with `createPool({ threads })({ tasks })`.
3. Call tasks through `call.*()` or `fastCall.*()` and optionally `send()`.
4. Shut down workers when finished.

Next: head to the installation guide or the quick start.
