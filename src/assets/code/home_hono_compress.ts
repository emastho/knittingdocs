import { serve } from "@hono/node-server";
import { brotliCompressSync } from "node:zlib";
import { Hono } from "hono";
import { createPool, isMain } from "knitting";

export const compress = (html: string) =>
  brotliCompressSync(html).byteLength;

if (isMain) {
  const pool = createPool({ threads: 1 })({ compress });
  const app = new Hono().get("/", async (c) => {
    const html = c.req.query("html") ?? "<h1>Hello from Hono</h1>";
    return c.json({ compressedBytes: await pool.call.compress(html) });
  });
  serve({ fetch: app.fetch, port: 3000 });
}
