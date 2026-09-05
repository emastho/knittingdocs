# Knitting 0.1.70

Release notes for the changes after the `0.1.63` npm release and through the
`0.1.70` npm release.

This release is a substantial transport and runtime update. The normal task
API is unchanged — define exported tasks, create a pool, call
`pool.call.<task>()`, and shut the pool down — while the paths underneath it now
move less data, spend less CPU waiting, and clean up more predictably.

### Scope note

`0.1.63` already shipped shared-submit work stealing enabled by default, along
with the `host.steal` and `host.stealRegionLanes` options and the `host.doorbell`
switch. Those are **not** new here. What `0.1.70` adds in that area is the
`host.stealClaim` discipline, the runtime-specific doorbell backends (Node
`uv_async_t`, Deno FFI, process-local), and a set of correctness fixes to the
claim and teardown paths. The sections below say which is which.

## Highlights

New public surface in `0.1.70`:

- Safer zero-copy ownership for `BufferReference`, replacing the removed
  `unsafe.BufferReferenceReturn` option.
- A pooled `KnittingSharedBuffer` allocator for shared byte regions.
- Request-body helpers that choose between an arena region and a moved buffer.
- Explicit shared-byte arguments and borrowed returns for advanced workloads
  (`unsafe.SharedBytes`, `unsafe.SharedArgs`, `sharedBytes()`,
  `pool.sharedArgBytes()`).
- `host.stealClaim` and `KNITTING_STEAL_CLAIM` for the region-claim discipline.
- `host.nativeDoorbell`, plus Deno and process-worker completion doorbells.

Behavior and packaging:

- More reliable worker shutdown, native-resource cleanup, and Windows/Bun
  process-worker behavior.
- Correctness fixes in the stealing claim, decode, and teardown paths.
- Refreshed native prebuilds and a manual npm publishing workflow.

## BufferReference and large binary values

`BufferReference` now follows an ownership-move model instead of exposing a
shared mutable alias:

- Constructing `new BufferReference(arrayBufferOrView)` detaches the source
  immediately. The reference becomes the owner of those bytes.
- Inputs can still move to same-process thread workers without a host-to-worker
  byte copy on Node, Deno, and Bun.
- A returned reference is adopted as an owned host value where the runtime can
  transfer backing-store ownership. Deno, Bun, and older Node backends use one
  safe host copy when cross-isolate ownership cannot be adopted.
- Releasing a reference revokes materialized aliases before dropping its native
  pin. If a buffer cannot be detached safely, the implementation keeps the
  memory alive rather than risk a use-after-free.
- Node native cleanup hooks remove worker-owned pointer and backing-store
  entries when an isolate is torn down. A host buffer that was already adopted
  keeps its own backing-store ownership.
- `BufferReference` remains thread-only. Use `ProcessSharedBuffer` for process
  workers or cross-process shared memory.

Ordinary top-level `Uint8Array` and `ArrayBuffer` results from thread workers
also use the safe ownership path automatically at 256 KiB and above. These
results stay valid after later calls and pool shutdown; applications do not
need to wrap them in `BufferReference`.

### API transition

The old `unsafe.BufferReferenceReturn` option and its `copy`/`borrow` controls
were removed. The replacement is:

- Use ordinary large binary returns for the safe automatic ownership path.
- Use `unsafe: { SharedBytes: true }` and `sharedBytes()` only when a task
  intentionally wants a short-lived borrowed return from the shared arena.
- Use `unsafe: { SharedArgs: true }` and `pool.sharedArgBytes()` only when the
  worker will consume the borrowed argument before it can be recycled.

## Shared-memory allocator

`knitting/shared-memory` now exports a pooled allocator built around
`KnittingSharedBuffer`:

```ts
import { createKnittingAllocator } from "knitting/shared-memory";

const allocator = createKnittingAllocator({
  arenaByteLength: 8 * 1024 * 1024,
});

const region = allocator.alloc(64 * 1024);
try {
  region.u8().set(input);
  await pool.call.process(region);
} finally {
  region.release();
}
```

The allocator provides:

- A shared arena with reusable regions and descriptors instead of copying the
  bytes into every call frame.
- `alloc()`, `allocUpTo()`, `allocOrRefer()`, `describe()`, `moveTo()`,
  `reconcile()`, `transport()`, `stats()`, `resetCounters()`, and typed views
  through `u8()`/`view()` on a region.
- Lazy region identities with a garbage-collection backstop. Reclamation is
  safe against late releases, and exhausted identities fall back to a
  standalone `SharedArrayBuffer` instead of evicting a live region or blocking
  the allocator.
- Explicit ownership rules: `moveTo()` transfers the release obligation;
  `describe()` is for inspection or a borrowed consumer handle.
- `attachKnittingAllocator()` and `createBodyReader()` for attaching a worker
  to the host allocator once and opening descriptors into `Uint8Array` views.
  The attached side exposes `adopt()` only — a consumer never allocates.
- `detectRegion()` for identifying a region that crossed a transport. Like
  `describe()`, it inspects without transferring ownership.

`arenaByteLength` defaults to `DEFAULT_ARENA_BYTE_LENGTH`, which is 2 MiB and is
exported from the same subpath. The example above passes 8 MiB explicitly. The
arena length is also the ceiling on a single pooled region.

## HTTP body transport helpers

The same subpath now exports helpers for reading request bodies directly into
the most suitable representation:

- `readBodyIntoBytes()` fills caller-provided storage.
- `readBodyIntoRegion()` streams or copies into a pooled
  `KnittingSharedBuffer`.
- `readBodyOrRefer()` returns a pooled region for smaller bodies and a moved
  `BufferReference` for larger bodies.
- `allocator.allocOrRefer()` wraps that choice in one disposable
  `KnittingBody` handle with a common ownership rule.

The defaults are tuned as starting points, not universal constants, and both
crossovers are exported so they can be referenced rather than retyped:

- Bodies at or above `HTTP_BODY_STREAM_THRESHOLD_BYTES` (192 KiB) with a known
  length can stream directly into the arena.
- Bodies at or above `HTTP_BODY_REFERENCE_THRESHOLD_BYTES` (2 MiB) use
  `BufferReference` when the request is being sent to a thread worker.

`maxByteLength` bounds the allocation and is enforced against both a declared
`Content-Length` and a chunked body read against the same cap, so an oversized
body is rejected before it can grow an unbounded allocation. Which helpers
require it differs, because only some of them can infer a bound:

- `readBodyIntoRegion()` defaults it to `allocator.arenaByteLength`, which is
  the most a pooled region can hold anyway.
- `readBodyIntoBytes()` requires it. It allocates through a caller-supplied
  function, so only the caller knows what that allocation can afford.
- `readBodyOrRefer()` and `allocator.allocOrRefer()` require it. They exist to
  handle bodies too large for the arena, so neither the pool nor the crossover
  implies a bound.

The host owns the body until the call settles. An early `using`-scope exit does
not recycle pooled bytes while a worker is still reading them. The worker
receives a `Uint8Array`; if it needs the bytes after the call, it must copy
them.

## Shared-byte arguments and returns

Advanced users can opt into the shared arena protocol:

```ts
using pool = createPool({
  threads: 4,
  unsafe: { SharedArgs: true, SharedBytes: true },
})({ render });

const input = pool.sharedArgBytes(byteLength);
input.set(source);
const output = await pool.call.render(input);
```

- `sharedBytes(size, zeroFill?)` allocates a borrowed return region inside a
  worker’s return arena.
- `pool.sharedArgBytes(size)` allocates a borrowed argument region in the
  shared submit arena when the pool topology supports it.
- Both features are opt-in and fall back to ordinary private buffers when the
  required shared path is unavailable — for example `sharedBytes()` outside a
  worker return lane, or `sharedArgBytes()` on a pool topology without a shared
  submit arena. The one exception is a compiled (Porffor) worker, which rejects
  an `unsafe` option outright rather than falling back.
- Borrowed return views are short-lived. Copy a result that must outlive the
  next batch of calls; the current return window is 32 large results per lane.
- Borrowed argument bytes must be consumed before the task’s first suspension
  point. Do not retain them across an `await`.
- `sharedBytes()` uses uninitialized memory unless `zeroFill` is requested, so
  tasks must write every byte they return.

## Work stealing and dispatch

Shared-submit work stealing is unchanged as a default and is **not new in this
release** — `0.1.63` already enabled it for compatible multi-worker thread and
process pools. Restated for context, the topology is:

1. The host publishes calls into one shared submit region.
2. Workers claim available regions when they are ready to run work.
3. Each worker keeps a private return region for its responses.
4. The worker that claims a task owns its completion; the host settles the
   corresponding promise from the shared pending registry.

Automatic selection is still disabled for one-worker pools, inliners, compiled
workers, explicitly private dispatcher/balancer configurations, and pools above
the 31-claimant protocol limit. `host.steal` and `KNITTING_STEAL` still force it
on or off. `host.stealRegionLanes` is likewise carried over from `0.1.63`; its
default is the widest region the lane budget allows, and a smaller value is
fairer for expensive tasks because a region is a batch.

New in `0.1.70`:

- `host.stealClaim` selects the region-claim discipline: `"dekker"` (the
  default, one intent slot per consumer) or `"cas-mask"` (one shared
  compare-and-swap mask). `KNITTING_STEAL_CLAIM=dekker` or
  `KNITTING_STEAL_CLAIM=cas-mask` sets it from the environment, and the explicit
  option wins over the environment.
- The discipline also sets the ceiling on an explicit `stealRegionLanes`.
  Dekker requires at least one spare region per live consumer, so it constrains
  the value more tightly than `cas-mask` does.

Correctness fixes in the same paths:

- Claimed work is now decoded in producer order. Both steal decoders previously
  handed a claimed region to the worker in reverse.
- Completed results are flushed before the next steal attempt.
- Retired lanes are reclaimed even when decoding fails.
- The protocol deactivates workers during teardown, so a dead worker cannot
  leave a claim permanently blocking the pool.

The private-lane dispatcher was tightened as well: active-lane tracking avoids
checking idle lanes, notifications are coalesced, and dispatch turns are
scheduled with `queueMicrotask` so queued work does not pay unnecessary timer
hops.

## Completion doorbells and idle CPU

`host.doorbell` itself shipped in `0.1.63`, where it meant `Atomics.waitAsync`
on Node and Bun and nothing anywhere else. `0.1.70` gives the other runtimes a
wake path of their own, so the host waits for a completion notification instead
of repeatedly polling an empty return mailbox in more places than before:

- Node and Bun thread workers use `Atomics.waitAsync`, as before.
- Deno now uses a thread-safe FFI callback, because its `waitAsync` does not
  wake an idle event loop. It is skipped when FFI permission is unavailable.
- Process workers now use a process-local completion transport. Atomics waiters
  are per-isolate, so they cannot be rung from another process.
- Node thread workers can additionally opt into the native `uv_async_t` bridge
  from the new `knitting_doorbell` addon with `host.nativeDoorbell: true`. It is
  **off by default**, does not apply to process workers, and is ignored when
  `host.doorbell` is `false`.
- Unsupported or denied configurations fall back to the portable polling path.
- `host.doorbell` defaults to enabled. Set `host: { doorbell: false }` to force
  polling for controlled comparisons, or for a pool that oversubscribes its
  machine — a doorbell only makes progress when the host gets scheduled, so once
  workers occupy every core a wake has to preempt one.

Worker parking was also hardened. Multi-worker pools do not spend a long spin
budget waiting for work, while the single-worker critical path retains a small
spin before parking. Bun on Windows avoids sub-2ms busy waits, and Windows
process workers use short polling intervals because address-based native wakes
cannot cross process mappings reliably.

## Shutdown, timeouts, and runtime reliability

- Worker transports now include a stop state. Shutdown asks the worker loop to
  stop, waits briefly for an acknowledgement, drains deferred native releases,
  and then terminates the worker if necessary.
- Node worker shutdown now gets the same acknowledgement opportunity needed to
  release native `BufferReference` pins safely. Process-worker teardown waits
  for exit before unmapping shared memory, with a bounded fallback timeout.
- Worker exits caused by an orderly stop are no longer reported as crashes.
- Promise-heavy worker loops yield correctly without turning progress into an
  unnecessary timer delay.
- Probe and corruption tests now account for worker boot time separately from
  the operation timeout, preventing startup cost from consuming the test’s
  fault budget.
- Runtime/process tests use longer, explicit budgets for slow process and
  shared-memory startup paths.

## Platform and package changes

- Deno-hosted process workers and Windows process workers automatically select
  named shared-memory mappings where anonymous descriptor inheritance is not
  reliable.
- Bun/Windows process-worker startup and parking behavior is covered by a
  dedicated check script.
- Native Node prebuilds now include the completion-doorbell addon alongside
  refreshed BufferReference pointer builds for Node ABI 127 and 137 on Linux
  x64, macOS x64/arm64, and Windows x64.
- Browser stubs were updated for the new native-doorbell and BufferReference
  paths; browser limitations remain unchanged: no process workers, native FFI,
  `BufferReference`, or `ProcessSharedBuffer`.
- The generated build output and unused benchmark/demo material were removed
  from source control. The package build now regenerates JavaScript and
  declarations before packing, and the `dts-bundle-generator` dev dependency is
  gone.
- `npm run test:bun` no longer excludes `tx-queue.test.ts`, so the Bun suite now
  runs every test file. That is why its reported count moved.
- A manual GitHub Actions npm publishing workflow was added for stable, beta,
  and nightly channels, with the package version set to `0.1.70`. The workflow
  publishes without committing the version back to the repository.

## Public surface changed in this release

Everything below is verified against the published `0.1.63` tarball, so each row
is genuinely a `0.1.63 → 0.1.70` delta.

### Removed

| Removed                          | Replacement                                        |
| -------------------------------- | -------------------------------------------------- |
| `unsafe.BufferReferenceReturn`   | Automatic ownership path, or `unsafe.SharedBytes`  |
| `"copy"` / `"borrow"` controls   | See the API transition section above               |

### Added — `knitting/unsafe`

| Export         | Notes                                                  |
| -------------- | ------------------------------------------------------ |
| `sharedBytes`  | `sharedBytes(byteLength, zeroFill = false)`; needs `unsafe: { SharedBytes: true }` |

### Added — `knitting/shared-memory`

| Export                                | Kind    |
| ------------------------------------- | ------- |
| `createKnittingAllocator`             | value   |
| `attachKnittingAllocator`             | value   |
| `KnittingSharedBuffer`                | class   |
| `DEFAULT_ARENA_BYTE_LENGTH`           | value (2 MiB) |
| `detectRegion`                        | value   |
| `createBodyReader`                    | value   |
| `readBodyIntoBytes`                   | value   |
| `readBodyIntoRegion`                  | value   |
| `readBodyOrRefer`                     | value   |
| `HTTP_BODY_STREAM_THRESHOLD_BYTES`    | value (192 KiB) |
| `HTTP_BODY_REFERENCE_THRESHOLD_BYTES` | value (2 MiB) |
| `KnittingAllocator`                   | type    |
| `KnittingAllocatorOptions`            | type    |
| `KnittingBufferDescriptor`            | type    |
| `KnittingBody`                        | type    |
| `KnittingBodyWire`                    | type    |
| `KnittingTransport`                   | type    |
| `ReadBodyOptions`                     | type    |
| `ReadBodyIntoBytesOptions`            | type    |
| `ReadBodyOrReferOptions`              | type    |
| `ReadBodyPayload`                     | type    |
| `RegionAllocator`                     | type    |

### Added — pool options and pool methods

| Name                    | Default    | Notes                                             |
| ----------------------- | ---------- | ------------------------------------------------- |
| `host.stealClaim`       | `"dekker"` | `"dekker"` or `"cas-mask"`                        |
| `host.nativeDoorbell`   | `false`    | Node thread workers only; needs `host.doorbell`   |
| `unsafe.SharedBytes`    | `false`    | Enables borrowed returns and `sharedBytes()`      |
| `unsafe.SharedArgs`     | `false`    | Enables `pool.sharedArgBytes()`                   |
| `pool.sharedArgBytes()` | —          | `(byteLength: number) => Uint8Array`              |

### Added — environment variables

| Variable               | Values                    | Equivalent option  |
| ---------------------- | ------------------------- | ------------------ |
| `KNITTING_STEAL_CLAIM` | `dekker`, `cas-mask`      | `host.stealClaim`  |

Unchanged from `0.1.63` and listed only to prevent a duplicate write-up:
`host.steal`, `host.stealRegionLanes`, `host.doorbell`, `KNITTING_STEAL`,
`KNITTING_DISPATCHER`, `host.dispatcher`, and the whole `Envelope` body-type
surface.

### Constants worth quoting in prose

| Constant                       | Value    | What it gates                                    |
| ------------------------------ | -------- | ------------------------------------------------ |
| `SHARED_RETURN_MIN_BYTES`      | 256 KiB  | Automatic ownership path for plain byte returns   |
| `SHARED_RETURN_BORROW_WINDOW`  | 32       | Borrowed returns kept before a region recycles     |
| `MAX_STEAL_CONSUMERS`          | 31       | Claimant ceiling before a pool falls back          |

These three are internal to `src/memory/payloadCodec.ts` and
`src/runtime/pool.ts` — quote the numbers, not the identifiers.

## Verification

The `0.1.70` package was built, packed, and smoke-tested from the npm registry.
The release validation passed:

- Deno: 460 passed, 0 failed, 7 ignored.
- Node: 499 passed, 0 failed, 3 skipped.
- Bun: 493 passed, 0 failed, 8 skipped.
- Browser end-to-end checks passed.
- A registry install of `knitting@0.1.70` imported the package and completed a
  real worker call successfully (`41` → `42`).

## Documentation references

The website documentation consulted for this release, with what each page needs:

- [Buffer reference](https://knittingdocs.netlify.app/guides/buffer-reference/)
  — rewrite for the ownership-move model; delete `BufferReferenceReturn` and its
  `copy`/`borrow` controls; add the automatic 256 KiB ownership path.
- [Shared memory](https://knittingdocs.netlify.app/guides/shared-memory/) — new
  allocator, `KnittingSharedBuffer`, and the HTTP body helpers. Largest gap.
- [Work stealing](https://knittingdocs.netlify.app/guides/work-stealing/) — add
  `host.stealClaim` and `KNITTING_STEAL_CLAIM` only. The rest of the page
  describes `0.1.63` behavior that has not changed.
- [Multi-threading](https://knittingdocs.netlify.app/guides/multi-threading/) —
  add the doorbell backends and `host.nativeDoorbell`.
- [Compiled workers](https://knittingdocs.netlify.app/guides/compiled-workers/)
  — unchanged behavior; confirm it still says compiled workers reject `host`.
- [Browser](https://knittingdocs.netlify.app/guides/browser/) — limitations are
  unchanged; only the stub list behind them moved.

The in-repo `README.md` was updated in this release to document `host.doorbell`,
`host.nativeDoorbell`, `host.stealRegionLanes`, and `host.stealClaim`, which it
had never covered. It is the closest thing to a reference for those four
options, so prefer it over older doc pages where they disagree.

Known gap not addressed here: `map.md` ships in the npm package and still lists
none of the modules added in this release.
