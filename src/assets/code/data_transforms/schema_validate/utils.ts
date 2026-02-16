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

export function makeValidPayload(i: number): string {
  const short = i.toString(36);
  const role = i % 9 === 0 ? "admin" : "user";

  return JSON.stringify({
    id: `u_${short}`,
    email: `${short}@knitting.dev`,
    displayName: `User ${short.toUpperCase()}`,
    age: 18 + (i % 60),
    roles: [role],
    marketingOptIn: i % 2 === 0,
  });
}

export function makePayload(i: number, invalidPercent: number): string {
  if (i % 100 >= invalidPercent) return makeValidPayload(i);

  switch (i % 4) {
    case 0:
      return '{"id":"broken"';
    case 1:
      return JSON.stringify({
        id: `u_${i}`,
        displayName: `User ${i}`,
        age: 33,
        roles: ["user"],
        marketingOptIn: true,
      });
    case 2:
      return JSON.stringify({
        id: `u_${i}`,
        email: `u_${i}@knitting.dev`,
        displayName: "x",
        age: "unknown",
        roles: ["user"],
      });
    default:
      return JSON.stringify({
        id: `u_${i}`,
        email: `u_${i}@knitting.dev`,
        displayName: `User ${i}`,
        age: 31,
        roles: ["owner"],
      });
  }
}

export function buildPayloads(count: number, invalidPercent: number): string[] {
  const cappedInvalid = Math.max(0, Math.min(95, Math.floor(invalidPercent)));
  const size = Math.max(0, Math.floor(count));
  const payloads = new Array<string>(size);
  for (let i = 0; i < size; i++) payloads[i] = makePayload(i, cappedInvalid);
  return payloads;
}

export function makeBatches<T>(values: T[], batchSize: number): T[][] {
  const size = Math.max(1, Math.floor(batchSize));
  const batches: T[][] = [];
  for (let i = 0; i < values.length; i += size) {
    batches.push(values.slice(i, i + size));
  }
  return batches;
}

export function mergeValidationSummary(
  a: ValidationSummary,
  b: ValidationSummary,
): ValidationSummary {
  return {
    valid: a.valid + b.valid,
    invalid: a.invalid + b.invalid,
  };
}

export function sameValidationSummary(
  a: ValidationSummary,
  b: ValidationSummary,
): boolean {
  return a.valid === b.valid && a.invalid === b.invalid;
}

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
