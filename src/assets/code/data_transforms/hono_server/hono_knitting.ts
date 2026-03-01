import { serve } from "@hono/node-server";
import { createPool } from "@vixeny/knitting";
import { Hono } from "hono";
import { issueJwt } from "./hono_components_jwt.ts";
import { renderSsrPage } from "./hono_componets_ssr.tsx";

const handlers = createPool({
})({
  issueJwt,
  renderSsrPage,
});

async function main() {
  const app = new Hono();

  app.get("/ping", (c) => {
    return c.json({
      ok: true,
      pong: true,
      runtime: process.release?.name ?? "unknown",
      ts: new Date().toISOString(),
    });
  });

  app.post("/ssr", async (c) => {
    const rawPayload = await c.req.text();
    if (rawPayload.trim().length === 0) {
      return c.json({ ok: false, reason: "body: expected JSON object" }, 400);
    }

    const html = await handlers.call.renderSsrPage(rawPayload);
    return c.html(html);
  });

  app.post("/jwt", async (c) => {
    const payload = await c.req.text().catch(() => null);

    if (!payload) {
      return c.json({ ok: false, reason: "body: expected JSON object" }, 400);
    }

    const responseJson = await handlers.call.issueJwt(payload);

    return c.body(responseJson ?? "Bad request", responseJson ? 200 : 400, {
      "content-type": "application/json; charset=utf-8",
    });
  });

  const server = serve({ fetch: app.fetch, port: 3000 }, (info) => {
    console.log("GET  /ping");
    console.log("POST /ssr   body: { name?, plan?, bio?, projects? }");
    console.log("POST /jwt   body: { user: { id, email?, role? }, ttlSec? }");
  });

  const close = () => {
    // IMPORTANT TO CLOSE CONNECTION
    handlers.shutdown();
    server.close();
  };

  process.on("SIGINT", close);
  process.on("SIGTERM", close);
}

main().catch((error) => {
  console.error(error);
  process.exitCode = 1;
});
