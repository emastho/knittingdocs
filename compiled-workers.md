# Compiled workers (Porffor)
URL: https://knittingdocs.netlify.app/guides/compiled-workers/

Ahead-of-time native workers compiled with Porffor — experimental.

A compiled worker is your task module compiled to a native executable by
[Porffor](https://github.com/CanadaHonk/porffor) and run as a child process.
Tasks are declared and called exactly as they are everywhere else; only the pool
options change.

**This backend is experimental.** Porffor is a young ahead-of-time compiler, the
artifact format is pre-release and changes with no compatibility path, and a
build produces native, unsandboxed code. Only compile and run task modules you
trust.

---

## Enabling it

For a task module `tasks.ts`, Knitting looks for `tasks.knt` beside it plus a
`tasks.knt.json` manifest. Two worker settings select the backend:

| Worker settings | Compilation behavior |
| --- | --- |
| `runtime: "compiled"` | Reuse a compatible `.knt`; build when missing, stale, or incompatible. |
| `processRuntime: "porffor"` | Select the backend and always rebuild once per pool. |
| Both together | Reuse a compatible `.knt`; build when missing, stale, or incompatible. |

```ts
import { createPool, isMain } from "knitting";

export const hello = (name: string) => "Hello " + name;

if (isMain) {
  using pool = createPool({
    worker: { runtime: "compiled", processRuntime: "porffor" },
  })({ hello });

  console.log(await pool.call.hello("World!")); // Hello World!
}
```

A multi-worker pool compiles once, then starts every native worker from the same
artifact.

---

## What the module may import

The task module is bundled and compiled for the native target, so its imports
are compiled too. Two limits follow from that, and both surface as build
failures rather than as runtime errors:

- From `knitting`, import only `task`, `isMain`, and `createPool`. Anything else
  — `checkCompiledWorker`, `Envelope`, `importTask` — has no worker-side
  equivalent and fails the build. Keep host-only calls in a different module.
- No runtime built-ins. Porffor implements a subset of JavaScript and does not
  provide `node:*` modules; importing one can hang the compiler rather than
  report an error. Plain local modules compile fine.

This is the practical ceiling on the backend today: compiled tasks are
self-contained computation, not glue code.

---

## Building ahead of time

Automatic builds resolve the compiler from `worker.compiled.compiler`, then
`PORFFOR_MAIN` / `PORF`, then `porf` on PATH. If none exists, Knitting downloads
a pinned compiler into `$XDG_CACHE_HOME/knitting` (or `~/.cache/knitting`).

To build it yourself instead:

```bash
bun run build:compiled --module tasks.ts --out tasks.knt --tasks addOne
```

Then point the pool at the artifact and turn generation off, so a deployment can
never shell out to a compiler:

```ts
const pool = createPool({
  worker: {
    runtime: "compiled",
    compiled: { artifact: "./build/tasks-linux-x64.knt", build: false },
  },
})({ addOne });
```

`worker.compiled.build` takes `true` (build only when the artifact cannot be
reused), `false` (never build; fail if it is unavailable), or `"always"`.
`worker.compiled.manifest` selects a non-default sidecar location.

Before spawning anything, Knitting requires the manifest to match the protocol
version, platform, architecture, source module, source timestamp, and requested
task names. `checkCompiledWorker(task, options)` reports that state read-only,
without building or executing.

---

## What crosses the boundary

| Value | Compiled worker |
| --- | --- |
| JSON primitives, arrays, plain objects | Copied — 1 MiB per call |
| `ArrayBuffer`, `DataView`, typed arrays | Copied |
| `ProcessSharedBuffer` | Mapped by the worker, not copied |
| `Promise<supported>` | Awaited on the host before dispatch |
| `Envelope`, `BufferReference`, BigInt typed arrays | Rejected |

Task functions must be synchronous — an async result is not supported. Strings
may use any BMP character; supplementary code points are rejected.

Prefer `ProcessSharedBuffer` for anything large. It is the one value the worker
maps directly rather than copying through the frame.

---

## Abort signals

Abort-aware tasks work on POSIX. The pool publishes an abort bitmap through
named shared memory, and the worker reads it natively — no polling round-trip to
the host.

```ts
export const search = task({
  abortSignal: true,
  f: (limit: number, signal) => {
    for (let i = 0; i < limit; i++) {
      if (signal.hasAborted()) return i;
    }
    return limit;
  },
});
```

`signal.now()` is a monotonic millisecond clock for measuring elapsed time
inside the task. Aborting stays cooperative: a task that never checks the signal
runs to completion. Windows has no implementation yet.

---

## Not supported

These fail during pool creation or invocation rather than degrading quietly:

| Option | Why |
| --- | --- |
| `inliner`, `host` | Host-side lanes have no compiled equivalent. |
| `permission` | The artifact is native code; runtime flags do not apply. |
| `worker.bootstrap` | No host module is imported into the worker. |
| `worker.timers`, task `timeout` | No timer scheduling inside the worker. |
| `importTask` | The compiler needs the task body at build time. |
| `payload`, `unsafe`, `source`, `workerExecArgv` | Transport options the frame protocol does not use. |
| `worker.processCommandPrefix`, `worker.processSharedMemory`, `worker.resolveAfterFinishingAll` | Process-worker options with no compiled equivalent. |

`worker.hardTimeoutMs` does work, because the host enforces it.

For anything on that list, use a process worker — see
[Process workers](/guides/process-workers/).
