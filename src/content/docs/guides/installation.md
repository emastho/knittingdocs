---
title: Installation
description: Requirements and how to install the package.
sidebar:
  order: 2
---

## Requirements

- Node.js 22+
- Deno 2+
- Bun (recent)

## Install

Knitting is published on JSR:

```bash
deno add jsr:@vixeny/knitting
```

## Local development in the repo

If you are working inside the knitting repository, you can import directly from
`./knitting.ts`:

```ts
import { createPool, isMain, task } from "./knitting.ts";
```
