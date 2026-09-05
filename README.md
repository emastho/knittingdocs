# Knitting documentation

This repository contains the Knitting documentation site. Knitting is a
shared-memory worker runtime for Node.js, Deno, Bun, and browser workers.

The guides describe the `0.1.70` public API, including pooled shared-memory
regions, safe large-binary ownership moves, work-stealing claim disciplines,
and runtime-specific completion doorbells.

## Run the site

```bash
npm install
npm run dev
```

Build and preview the static site with:

```bash
npm run build
npm run preview
```

## Runtime reference

Install the runtime package in an application with:

```bash
npm install knitting@0.1.70
```

The normal task API is unchanged:

```ts
import { createPool, isMain } from "knitting";

export const double = (value: number) => value * 2;

if (isMain) {
  using pool = createPool({ threads: 2 })({ double });
  console.log(await pool.call.double(21)); // 42
}
```

For compatible multi-worker pools, shared-submit work stealing is enabled by
default. The relevant host options are:

```ts
host: {
  steal?: boolean,
  stealRegionLanes?: number,
  stealClaim?: "dekker" | "cas-mask",
  doorbell?: boolean,
  nativeDoorbell?: boolean,
}
```

`stealClaim` defaults to `"dekker"`; `KNITTING_STEAL_CLAIM` selects the same
discipline from the environment. `doorbell` defaults to enabled and uses the
best supported completion wake path, with polling fallback. On Node thread
workers, `nativeDoorbell` opts into the optional `uv_async_t` addon bridge and
is ignored when `doorbell` is disabled.

Large top-level `Uint8Array` and `ArrayBuffer` returns use the safe ownership
path automatically at 256 KiB and above. Use `BufferReference` for an explicit
thread-only input move.

Advanced shared-byte paths are opt-in:

```ts
using pool = createPool({
  threads: 4,
  unsafe: { SharedArgs: true, SharedBytes: true },
})({ render });

const input = pool.sharedArgBytes(byteLength);
input.set(source);
const output = await pool.call.render(input);
```

Borrowed argument bytes must be consumed before the task's first `await`, and
borrowed return views must be copied if they need to outlive the current return
window. See the [shared memory guide](https://knittingdocs.netlify.app/guides/shared-memory/)
and [buffer reference guide](https://knittingdocs.netlify.app/guides/buffer-reference/)
for ownership details.

## Repository layout

- `src/content/docs/` — Starlight guides and examples.
- `src/lib/llms.ts` — generated documentation summaries for `llms.txt`.
- `public/knitting.js` — browser bundle used by the browser guide and smoke test.
- `public/_headers` — cross-origin isolation headers for browser examples.
