import { sign } from "hono/jwt";
import { task } from "@vixeny/knitting";
import { z } from "zod";

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
    return parsed;
  } catch {
    ctx.addIssue({
      code: z.ZodIssueCode.custom,
      message: "payload: expected JSON object",
    });
    return z.NEVER;
  }
});

const JwtUserSchema = z.object({
  id: z.string().min(1),
  email: z.string().email().optional(),
  role: z.string().min(1).optional(),
});

const TtlSecSchema = z.preprocess((value) => {
  const n = Number(value);
  if (!Number.isFinite(n)) return 900;
  return Math.max(30, Math.min(86_400, Math.floor(n)));
}, z.number().int());

const JwtPayloadSchema = z.object({
  user: JwtUserSchema,
  ttlSec: TtlSecSchema.optional().default(900),
});

export async function issueJwtHost(rawPayload: string): Promise<string | null> {
  const parsedResult = ParsedJsonObjectSchema.safeParse(rawPayload);
  if (!parsedResult.success) {
    return null;
  }

  const payloadResult = JwtPayloadSchema.safeParse(parsedResult.data);
  if (!payloadResult.success) {
    return null;
  }

  const { user, ttlSec } = payloadResult.data;
  const now = Math.floor(Date.now() / 1000);
  const exp = now + ttlSec;

  const token = await sign(
    {
      sub: user.id,
      email: user.email,
      role: user.role ?? "member",
      iat: now,
      exp,
    },
    process.env.secret ?? "hello",
  );

  return JSON.stringify({
    ok: true,
    token,
    sub: user.id,
    exp,
  });
}

export const issueJwt = task({
  f: issueJwtHost,
});
