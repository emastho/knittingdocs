---
title: Defining tasks
description: Wrap functions with task() and export them.
sidebar:
  order: 1
---

`task({ f, href?, timeout? })` wraps a function so workers can discover and run
it. Tasks should be defined at module scope and exported.

## Guidelines

- Define tasks at module scope (no conditional exports).
- Export tasks from the module where they are defined.
- Prefer a single argument; use a tuple or object for multiple values.

## Simple task

```ts
import { task } from "@vixeny/knitting";

export const hello = task({
  f: async () => "hello",
});
```

## Task with arguments

```ts
export const add = task<[number, number], number>({
  f: async ([a, b]) => a + b,
});
```

## Single-task pool

```ts
import { isMain, task } from "@vixeny/knitting";

export const world = task({
  f: async () => "world",
}).createPool({
  threads: 2,
});

if (isMain) {
  const results = await Promise.all([world.call()]);
  console.log("Results:", results);
  world.shutdown();
}
```

## Optional timeout

```ts
export const maybeSlow = task<string, string>({
  timeout: { time: 50, default: "timeout" },
  f: async (value) => value,
});
```

Available fields:

- `time` (number, ms) required.
- `default` resolves with the provided value on timeout.
- `maybe: true` resolves with `undefined` on timeout.
- `error` rejects with the provided error on timeout.

If none of `default`, `maybe`, or `error` are set, the call rejects with
`Error("Task timeout")`.

## Note

Timeouts race the task result; the underlying work may still complete even if
its promise resolves or rejects early.
