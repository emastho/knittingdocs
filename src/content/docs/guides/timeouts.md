---
title: Task timeouts
description: Add time limits to task execution.
sidebar:
  order: 9
---

You can add a timeout to any task with the `timeout` option.

## Numeric timeout

A number is interpreted as milliseconds. If the time is reached, the call
rejects with `Error("Task timeout")`. A negative number disables the timeout.

```ts
export const slow = task({
  timeout: 100,
  f: async () => "ok",
});
```

## Object timeout

```ts
export const maybeSlow = task<string, string>({
  timeout: { time: 50, default: "fallback" },
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
