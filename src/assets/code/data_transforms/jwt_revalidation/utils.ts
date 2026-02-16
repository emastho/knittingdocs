import { task } from "@vixeny/knitting";

export const DEMO_JWT_SECRET = "knitting-docs-demo-hs256-secret";

const DEFAULT_TTL_SEC = 180;
const DEFAULT_RENEW_WINDOW_SEC = 30;
const MIN_TTL_SEC = 10;
const MAX_TTL_SEC = 86_400;
const MAX_RENEW_WINDOW_SEC = 3_600;

const encoder = new TextEncoder();
const decoder = new TextDecoder();
const keyCache = new Map<string, Promise<CryptoKey>>();

type JwtHeader = {
  alg: "HS256";
  typ: "JWT";
};

export type JwtClaims = {
  sub: string;
  sid: string;
  scope: string[];
  iat: number;
  exp: number;
  renewUntil: number;
};

export type RevalidateRequest = {
  token: string;
  nowSec?: number;
  ttlSec?: number;
  renewWindowSec?: number;
};

export type RevalidateResponse =
  | {
    ok: true;
    renewed: boolean;
    token: string;
    sub: string;
    sid: string;
    exp: number;
    canRenew: boolean;
  }
  | {
    ok: false;
    renewed: false;
    reason: string;
  };

export type RenewalSummary = {
  ok: number;
  renewed: number;
  rejected: number;
  outputBytes: number;
};

export type DemoRequestOptions = {
  count: number;
  nowSec?: number;
  invalidPercent?: number;
  ttlSec?: number;
  renewWindowSec?: number;
};

export function makeBatches<T>(values: T[], batchSize: number): T[][] {
  const size = Math.max(1, Math.floor(batchSize));
  const batches: T[][] = [];
  for (let i = 0; i < values.length; i += size) {
    batches.push(values.slice(i, i + size));
  }
  return batches;
}

export function mergeRenewalSummary(
  a: RenewalSummary,
  b: RenewalSummary,
): RenewalSummary {
  return {
    ok: a.ok + b.ok,
    renewed: a.renewed + b.renewed,
    rejected: a.rejected + b.rejected,
    outputBytes: a.outputBytes + b.outputBytes,
  };
}

export function sameRenewalSummary(
  a: RenewalSummary,
  b: RenewalSummary,
): boolean {
  return a.ok === b.ok &&
    a.renewed === b.renewed &&
    a.rejected === b.rejected &&
    a.outputBytes === b.outputBytes;
}

function clampInt(
  value: unknown,
  fallback: number,
  min: number,
  max: number,
): number {
  const numberValue = Number(value);
  if (!Number.isFinite(numberValue)) return fallback;
  const integer = Math.floor(numberValue);
  if (integer < min) return min;
  if (integer > max) return max;
  return integer;
}

function isRecord(value: unknown): value is Record<string, unknown> {
  return typeof value === "object" && value !== null && !Array.isArray(value);
}

function bytesToBase64Url(bytes: Uint8Array): string {
  let binary = "";
  for (let i = 0; i < bytes.length; i++) {
    binary += String.fromCharCode(bytes[i]!);
  }
  const base64 = btoa(binary);
  return base64.replace(/\+/g, "-").replace(/\//g, "_").replace(/=+$/g, "");
}

function base64UrlToBytes(base64url: string): Uint8Array {
  const normalized = base64url.replace(/-/g, "+").replace(/_/g, "/");
  const pad = (4 - (normalized.length % 4)) % 4;
  const padded = normalized + "=".repeat(pad);
  const binary = atob(padded);
  const out = new Uint8Array(binary.length);
  for (let i = 0; i < binary.length; i++) {
    out[i] = binary.charCodeAt(i);
  }
  return out;
}

function safeParseJson(raw: string): unknown | null {
  try {
    return JSON.parse(raw) as unknown;
  } catch {
    return null;
  }
}

function fixedTimeEqual(a: Uint8Array, b: Uint8Array): boolean {
  if (a.length !== b.length) return false;
  let diff = 0;
  for (let i = 0; i < a.length; i++) {
    diff |= a[i]! ^ b[i]!;
  }
  return diff === 0;
}

function parseClaims(value: unknown): JwtClaims | null {
  if (!isRecord(value)) return null;
  const { sub, sid, scope, iat, exp, renewUntil } = value;

  if (typeof sub !== "string" || sub.length === 0) return null;
  if (typeof sid !== "string" || sid.length === 0) return null;
  if (!Array.isArray(scope) || scope.length === 0) return null;
  if (!scope.every((item) => typeof item === "string" && item.length > 0)) {
    return null;
  }
  if (
    !Number.isInteger(iat) || !Number.isInteger(exp) ||
    !Number.isInteger(renewUntil)
  ) {
    return null;
  }
  if (exp <= iat) return null;
  if (renewUntil < exp) return null;

  return { sub, sid, scope: [...scope], iat, exp, renewUntil };
}

async function getHmacKey(secret: string): Promise<CryptoKey> {
  let keyPromise = keyCache.get(secret);
  if (!keyPromise) {
    keyPromise = crypto.subtle.importKey(
      "raw",
      encoder.encode(secret),
      { name: "HMAC", hash: "SHA-256" },
      false,
      ["sign"],
    );
    keyCache.set(secret, keyPromise);
  }
  return keyPromise;
}

async function signInput(
  signingInput: string,
  secret: string,
): Promise<string> {
  const key = await getHmacKey(secret);
  const signature = await crypto.subtle.sign(
    "HMAC",
    key,
    encoder.encode(signingInput),
  );
  return bytesToBase64Url(new Uint8Array(signature));
}

async function verifyToken(
  token: string,
  secret: string,
): Promise<JwtClaims | null> {
  try {
    const parts = token.split(".");
    if (parts.length !== 3) return null;
    const [headerPart, payloadPart, signaturePart] = parts;
    if (!headerPart || !payloadPart || !signaturePart) return null;

    const headerRaw = safeParseJson(
      decoder.decode(base64UrlToBytes(headerPart)),
    );
    if (!isRecord(headerRaw)) return null;
    if (headerRaw.alg !== "HS256") return null;
    if (headerRaw.typ !== "JWT") return null;

    const expectedSignature = await signInput(
      `${headerPart}.${payloadPart}`,
      secret,
    );
    const expectedBytes = base64UrlToBytes(expectedSignature);
    const providedBytes = base64UrlToBytes(signaturePart);
    if (!fixedTimeEqual(expectedBytes, providedBytes)) return null;

    const payloadRaw = safeParseJson(
      decoder.decode(base64UrlToBytes(payloadPart)),
    );
    return parseClaims(payloadRaw);
  } catch {
    return null;
  }
}

function parseRevalidateRequest(rawRequest: string): RevalidateRequest | null {
  const parsed = safeParseJson(rawRequest);
  if (!isRecord(parsed)) return null;
  if (typeof parsed.token !== "string" || parsed.token.length === 0) {
    return null;
  }

  return {
    token: parsed.token,
    nowSec: parsed.nowSec as number | undefined,
    ttlSec: parsed.ttlSec as number | undefined,
    renewWindowSec: parsed.renewWindowSec as number | undefined,
  };
}

function shouldRenewToken(
  claims: JwtClaims,
  nowSec: number,
  renewWindowSec: number,
): boolean {
  if (nowSec > claims.renewUntil) return false;
  return nowSec >= claims.exp - renewWindowSec;
}

function responseError(reason: string): RevalidateResponse {
  return { ok: false, renewed: false, reason };
}

export async function issueTokenHost(
  claims: JwtClaims,
  secret = DEMO_JWT_SECRET,
): Promise<string> {
  const header: JwtHeader = { alg: "HS256", typ: "JWT" };
  const headerPart = bytesToBase64Url(encoder.encode(JSON.stringify(header)));
  const payloadPart = bytesToBase64Url(encoder.encode(JSON.stringify(claims)));
  const signingInput = `${headerPart}.${payloadPart}`;
  const signaturePart = await signInput(signingInput, secret);

  return `${signingInput}.${signaturePart}`;
}

export async function revalidateTokenObjectHost(
  rawRequest: string,
  secret = DEMO_JWT_SECRET,
): Promise<RevalidateResponse> {
  const request = parseRevalidateRequest(rawRequest);
  if (!request) {
    return responseError("payload: expected JSON { token, nowSec? }");
  }

  const nowSec = clampInt(
    request.nowSec,
    Math.floor(Date.now() / 1000),
    1,
    2_147_483_647,
  );
  const ttlSec = clampInt(
    request.ttlSec,
    DEFAULT_TTL_SEC,
    MIN_TTL_SEC,
    MAX_TTL_SEC,
  );
  const renewWindowSec = clampInt(
    request.renewWindowSec,
    DEFAULT_RENEW_WINDOW_SEC,
    0,
    MAX_RENEW_WINDOW_SEC,
  );

  const claims = await verifyToken(request.token, secret);
  if (!claims) {
    return responseError("token: invalid signature, claims, or format");
  }

  const renewable = shouldRenewToken(claims, nowSec, renewWindowSec);
  if (renewable) {
    const renewedExp = Math.min(nowSec + ttlSec, claims.renewUntil);
    if (renewedExp > nowSec) {
      const renewedClaims: JwtClaims = {
        ...claims,
        iat: nowSec,
        exp: renewedExp,
      };
      const renewedToken = await issueTokenHost(renewedClaims, secret);
      return {
        ok: true,
        renewed: true,
        token: renewedToken,
        sub: claims.sub,
        sid: claims.sid,
        exp: renewedExp,
        canRenew: nowSec < claims.renewUntil,
      };
    }
  }

  if (nowSec > claims.exp) {
    return responseError("token: expired and outside renewal policy");
  }

  return {
    ok: true,
    renewed: false,
    token: request.token,
    sub: claims.sub,
    sid: claims.sid,
    exp: claims.exp,
    canRenew: nowSec <= claims.renewUntil,
  };
}

export async function revalidateTokenHost(rawRequest: string): Promise<string> {
  const response = await revalidateTokenObjectHost(rawRequest);
  return JSON.stringify(response);
}

export const revalidateToken = task<string, string>({
  f: revalidateTokenHost,
});

function addSummary(
  totals: RenewalSummary,
  response: RevalidateResponse,
  outputBytes: number,
): RenewalSummary {
  const next: RenewalSummary = {
    ok: totals.ok,
    renewed: totals.renewed,
    rejected: totals.rejected,
    outputBytes: totals.outputBytes + outputBytes,
  };

  if (!response.ok) {
    next.rejected += 1;
    return next;
  }

  next.ok += 1;
  if (response.renewed) next.renewed += 1;
  return next;
}

export async function revalidateTokenBatchFastHost(
  rawRequests: string[],
): Promise<RenewalSummary> {
  let totals: RenewalSummary = {
    ok: 0,
    renewed: 0,
    rejected: 0,
    outputBytes: 0,
  };

  for (let i = 0; i < rawRequests.length; i++) {
    const response = await revalidateTokenObjectHost(rawRequests[i]!);
    const responseJson = JSON.stringify(response);
    totals = addSummary(totals, response, responseJson.length);
  }

  return totals;
}

export const revalidateTokenBatchFast = task<string[], RenewalSummary>({
  f: revalidateTokenBatchFastHost,
});

export function summarizeJsonResponses(rawResponses: string[]): RenewalSummary {
  const totals: RenewalSummary = {
    ok: 0,
    renewed: 0,
    rejected: 0,
    outputBytes: 0,
  };

  for (let i = 0; i < rawResponses.length; i++) {
    const raw = rawResponses[i]!;
    totals.outputBytes += raw.length;

    const parsed = safeParseJson(raw);
    if (!isRecord(parsed) || parsed.ok !== true) {
      totals.rejected += 1;
      continue;
    }

    totals.ok += 1;
    if (parsed.renewed === true) totals.renewed += 1;
  }

  return totals;
}

function tamperToken(token: string): string {
  const chars = token.split("");
  const last = chars.length - 1;
  chars[last] = chars[last] === "a" ? "b" : "a";
  return chars.join("");
}

export async function buildDemoRevalidateRequests(
  options: DemoRequestOptions,
): Promise<string[]> {
  const count = clampInt(options.count, 1, 1, 5_000_000);
  const nowSec = clampInt(
    options.nowSec,
    Math.floor(Date.now() / 1000),
    1,
    2_147_483_647,
  );
  const ttlSec = clampInt(
    options.ttlSec,
    DEFAULT_TTL_SEC,
    MIN_TTL_SEC,
    MAX_TTL_SEC,
  );
  const renewWindowSec = clampInt(
    options.renewWindowSec,
    DEFAULT_RENEW_WINDOW_SEC,
    0,
    MAX_RENEW_WINDOW_SEC,
  );
  const invalidPercent = clampInt(options.invalidPercent, 10, 0, 95);

  const renewable = await issueTokenHost({
    sub: "u_demo_renewable",
    sid: "s_renewable",
    scope: ["read", "profile"],
    iat: nowSec - 70,
    exp: nowSec + Math.max(5, renewWindowSec - 3),
    renewUntil: nowSec + 900,
  });

  const fresh = await issueTokenHost({
    sub: "u_demo_fresh",
    sid: "s_fresh",
    scope: ["read"],
    iat: nowSec - 10,
    exp: nowSec + 180,
    renewUntil: nowSec + 900,
  });

  const expiredRenewable = await issueTokenHost({
    sub: "u_demo_expired_grace",
    sid: "s_expired_grace",
    scope: ["read", "write"],
    iat: nowSec - 200,
    exp: nowSec - 4,
    renewUntil: nowSec + 240,
  });

  const expiredHard = await issueTokenHost({
    sub: "u_demo_expired_hard",
    sid: "s_expired_hard",
    scope: ["read"],
    iat: nowSec - 500,
    exp: nowSec - 30,
    renewUntil: nowSec - 3,
  });

  const badSignature = tamperToken(fresh);
  const malformed = "not-a-jwt";

  const requests = new Array<string>(count);
  for (let i = 0; i < count; i++) {
    const withinInvalid = i % 100 < invalidPercent;
    let token: string;

    if (withinInvalid) {
      token = i % 2 === 0 ? badSignature : malformed;
    } else {
      switch (i % 4) {
        case 0:
          token = renewable;
          break;
        case 1:
          token = fresh;
          break;
        case 2:
          token = expiredRenewable;
          break;
        default:
          token = expiredHard;
      }
    }

    requests[i] = JSON.stringify({
      token,
      nowSec,
      ttlSec,
      renewWindowSec,
    });
  }

  return requests;
}
