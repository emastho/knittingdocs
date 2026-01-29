---
title: Batching and send()
description: Queue calls and flush once.
sidebar:
  order: 6
---

`call.*()` enqueues work and usually wakes the dispatcher automatically. When
you want to submit a large batch, calling `send()` once after the batch makes
the intent explicit and can reduce latency under load.

```ts
const jobs = Array.from({ length: 1_000 }, () => call.hello());

// Flush the batch explicitly.
send();

const results = await Promise.all(jobs);
```
