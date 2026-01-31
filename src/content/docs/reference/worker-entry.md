---
title: Worker entry
description: How workers discover tasks and start the loop.
sidebar:
  order: 5
---

By default, knitting spawns workers that import its internal entry module. You
can override this with `source` to run your own worker entry module.

The worker entry is responsible for calling `workerMainLoop(workerData)`. If you
import it directly, the module auto-starts the loop when running inside a worker
thread.

Use this when you need custom initialization inside worker threads.
