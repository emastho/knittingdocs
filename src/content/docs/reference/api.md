---
title: API
description: Public exports and their signatures.
sidebar:
  order: 1
---

Knitting exports four public APIs:

- `task`
- `createPool`
- `isMain`
- `workerMainLoop`

## task

```ts
task<A, B>({ f, href?, timeout? }) => Task<A, B>
```

Wraps a function so it can be registered and executed in workers. The returned
object also includes `createPool(options?)` for single-task pools.

`href` can override the module URL used for task discovery when needed.

## createPool

```ts
createPool(options)(tasks) => {
  call,
  fastCall,
  send,
  shutdown,
}
```

Creates a worker pool. `call` and `fastCall` map each task name to a function
that returns a promise. `fastCall` uses the fast calling path but shares the
same signature. `send()` flushes the batch, and `shutdown()` terminates all
workers.

## isMain

Boolean flag that is `true` in the main thread and `false` in worker threads.

## workerMainLoop

```ts
workerMainLoop(workerData) => Promise<void>
```

Runs the worker event loop. Use this if you provide a custom worker entry via
`source`.
