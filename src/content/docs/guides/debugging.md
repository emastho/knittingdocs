---
title: Debugging
description: Enable logging and extra diagnostics.
sidebar:
  order: 12
---

Use the `debug` option in `createPool` to enable logging helpers.

```ts
const pool = createPool({
  threads: 2,
  debug: {
    extras: true,
    logMain: false,
    logHref: true,
    logImportedUrl: true,
  },
})({ add });
```

Available flags:

- `extras`: enable extra warnings (for example, calling `createPool` in a
  worker).
- `logMain`: log main dispatcher events.
- `logHref`: log the worker entry module URL.
- `logImportedUrl`: log task module URLs detected by the worker.
