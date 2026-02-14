import React from "react";
import { renderToString } from "react-dom/server";
import { task } from "@vixeny/knitting";
import { z } from "zod";

type SsrInput = {
  name: string;
  plan: "free" | "pro";
  bio: string;
  projects: number;
};

function UserCard({ user }: { user: SsrInput & { updatedAt: string } }) {
  return (
    <html lang="en">
      <head>
        <meta charSet="utf-8" />
        <meta name="viewport" content="width=device-width, initial-scale=1" />
        <title>{`${user.name} - SSR Card`}</title>
        <style>
          {`
          body { margin: 0; font-family: ui-sans-serif, system-ui, sans-serif; background: #f7f8fa; color: #111827; }
          main { min-height: 100vh; display: grid; place-items: center; padding: 24px; }
          article { width: min(680px, 100%); background: #fff; border: 1px solid #e5e7eb; border-radius: 16px; padding: 20px; }
          h1 { margin: 0 0 8px; font-size: 1.4rem; }
          p { margin: 0 0 10px; line-height: 1.45; }
          .meta { color: #4b5563; font-size: 0.92rem; display: flex; gap: 12px; flex-wrap: wrap; }
          .pill { display: inline-block; background: #eef2ff; color: #4338ca; border-radius: 999px; padding: 4px 10px; font-weight: 600; }
        `}
        </style>
      </head>
      <body>
        <main>
          <article>
            <h1>{user.name}</h1>
            <p>{user.bio}</p>
            <div className="meta">
              <span className="pill">{user.plan.toUpperCase()} plan</span>
              <span>{user.projects.toLocaleString()} projects</span>
              <span>Rendered at {user.updatedAt}</span>
            </div>
          </article>
        </main>
      </body>
    </html>
  );
}

const ParsedJsonObjectSchema = z.string().transform((raw, ctx) => {
  try {
    const parsed = JSON.parse(raw) as unknown;
    if (
      typeof parsed !== "object" || parsed === null || Array.isArray(parsed)
    ) {
      ctx.addIssue({
        code: z.ZodIssueCode.custom,
        message: "payload: expected JSON object",
      });
      return z.NEVER;
    }
    return parsed as Record<string, unknown>;
  } catch {
    ctx.addIssue({
      code: z.ZodIssueCode.custom,
      message: "payload: expected JSON object",
    });
    return z.NEVER;
  }
});

const RawSsrInputSchema = z.object({
  name: z.preprocess((value) => {
    if (typeof value !== "string") return undefined;
    const normalized = value.trim();
    return normalized.length > 0 ? normalized : undefined;
  }, z.string().optional()),
  plan: z.preprocess(
    (value) => (value === "free" || value === "pro" ? value : undefined),
    z.enum(["free", "pro"]).optional(),
  ),
  bio: z.preprocess((value) => {
    if (typeof value !== "string") return undefined;
    const normalized = value.trim();
    return normalized.length > 0 ? normalized : undefined;
  }, z.string().optional()),
  projects: z.preprocess((value) => {
    const numberValue = Number(value);
    if (!Number.isFinite(numberValue)) return undefined;
    return Math.max(0, Math.min(100_000, Math.floor(numberValue)));
  }, z.number().int().optional()),
});

const SsrInputSchema = RawSsrInputSchema.transform(
  (value): SsrInput => ({
    name: value.name ?? "Anonymous",
    plan: value.plan ?? "free",
    bio: value.bio ?? "No bio yet.",
    projects: value.projects ?? 0,
  }),
);

export function renderSsrPageHost(rawPayload: string): string {
  const parsed = ParsedJsonObjectSchema.safeParse(rawPayload);
  const user: SsrInput = SsrInputSchema.parse(
    parsed.success ? parsed.data : {},
  );
  const html = renderToString(
    <UserCard user={{ ...user, updatedAt: new Date().toISOString() }} />,
  );

  return `<!doctype html>${html}`;
}

export const renderSsrPage = task({
  f: renderSsrPageHost,
});
