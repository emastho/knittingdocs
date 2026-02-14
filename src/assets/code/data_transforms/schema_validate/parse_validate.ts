import { task } from "@vixeny/knitting";
import { z } from "zod";

const UserSchema = z.object({
  id: z.string().min(1),
  email: z.string().email(),
  displayName: z.string().min(2).max(80),
  age: z.number().int().min(13).max(120),
  roles: z.array(z.enum(["user", "admin", "moderator"])).default(["user"]),
  marketingOptIn: z.boolean().default(false),
});

export type User = z.infer<typeof UserSchema>;

export type ParseValidateResult =
  | { ok: true; value: User }
  | { ok: false; issues: string[] };

export type ValidationSummary = {
  valid: number;
  invalid: number;
};

function toIssues(error: z.ZodError): string[] {
  return error.issues.map((issue) => {
    const path = issue.path.length > 0 ? issue.path.join(".") : "payload";
    return `${path}: ${issue.message}`;
  });
}

export function parseAndValidateHost(rawPayload: string): ParseValidateResult {
  let parsed: unknown;
  try {
    parsed = JSON.parse(rawPayload) as unknown;
  } catch {
    return { ok: false, issues: ["payload: invalid JSON string"] };
  }

  const result = UserSchema.safeParse(parsed);
  if (!result.success) {
    return { ok: false, issues: toIssues(result.error) };
  }

  return { ok: true, value: result.data };
}

export const parseAndValidate = task<string, ParseValidateResult>({
  f: parseAndValidateHost,
});

export function parseAndValidateFastHost(rawPayload: string): boolean {
  let parsed: unknown;
  try {
    parsed = JSON.parse(rawPayload) as unknown;
  } catch {
    return false;
  }

  return UserSchema.safeParse(parsed).success;
}

export function parseAndValidateBatchFastHost(
  rawPayloads: string[],
): ValidationSummary {
  let valid = 0;
  let invalid = 0;

  for (let i = 0; i < rawPayloads.length; i++) {
    if (parseAndValidateFastHost(rawPayloads[i]!)) {
      valid++;
    } else {
      invalid++;
    }
  }

  return { valid, invalid };
}

export const parseAndValidateBatchFast = task<string[], ValidationSummary>({
  f: parseAndValidateBatchFastHost,
});
