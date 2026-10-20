# Knitting documentation

This repository contains the Knitting documentation site. Knitting is a
shared-memory worker runtime for Node.js, Deno, Bun, and browser workers.
You can also try thread pools on Andromeda 0.1.14; support is experimental.

The documentation baseline comes from the resolved `@vixeny/knitting` dependency
at build time; features marked `since` may require a newer release. The guides
cover adaptive ticket claims,
pooled shared-memory regions, safe large-binary ownership moves, and
runtime-specific completion doorbells.

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
npm install knitting@0.1.77
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
default, except on Andromeda. The relevant host options are:

```ts
host: {
  steal?: boolean,
  stealRegionLanes?: number,
  stealClaim?: "ticket" | "dekker",
  stealSingleClaimMicroseconds?: number,
  doorbell?: boolean,
  nativeDoorbell?: boolean,
}
```

`stealClaim` defaults to `"ticket"`. You can also choose it through
`KNITTING_STEAL_CLAIM`. Unknown values, including the old `"cas-mask"` option,
cause pool creation to throw. `stealSingleClaimMicroseconds` defaults to `0`,
which turns adaptation off. Try `20` when your workload mixes slow and fast
tasks, then measure whether it helps.

`doorbell` is enabled by default. It uses the runtime's best available way to
wake the host when a result is ready, falling back to polling. On Node thread
workers, `nativeDoorbell` opts into the optional `uv_async_t` addon bridge and
is ignored when `doorbell` is disabled.

To run on Andromeda, bundle Knitting into one ESM file and call
`setModuleUrl(import.meta.url)` in your task modules and app entry. Pools use
private submit lanes by default. Andromeda doesn't support process workers,
`ProcessSharedBuffer`, or separate worker permissions. The
[Andromeda guide](src/content/docs/guides/andromeda.mdx) walks through examples
with one file and with separate task modules.

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

## Agent documentation

`llms.txt` is a compact task router with essential coding rules and a runnable
example. `llms-full.txt` keeps the detailed implementation reference and all
maintained pages. Each indexed page is also generated as plain Markdown at
`/documents/<page-id>.md`, with embedded code and tables expanded. Experimental
runtime examples state their own tested versions.

After building, check task routes, generated links, the debugging anchor,
Markdown coverage, and version metadata with:

```bash
npm run build
npm run check:llms
```

These are structural navigation checks, not agent performance evaluations.
To compare agent usability, run the same implementation tasks against each index
version and record relevant-page retrieval, runnable code, retrieval/token cost,
unnecessary options, invented APIs, and first-pass success over repeated runs.
