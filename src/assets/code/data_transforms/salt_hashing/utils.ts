import { task } from "@vixeny/knitting";

const encoder = new TextEncoder();
const decoder = new TextDecoder();

const DEFAULT_ITERATIONS = 120_000;
const DEFAULT_KEY_BYTES = 32;
const DEFAULT_SALT_BYTES = 16;
const MIN_ITERATIONS = 10_000;
const MAX_ITERATIONS = 2_000_000;
const MIN_KEY_BYTES = 16;
const MAX_KEY_BYTES = 64;
const MIN_SALT_BYTES = 8;
const MAX_SALT_BYTES = 32;

export type HashRequest = {
  password: string;
  iterations?: number;
  keyBytes?: number;
  saltBase64?: string;
};

export type HashResponse = {
  record: string;
  algorithm: "pbkdf2-sha256";
  iterations: number;
  keyBytes: number;
  saltBase64: string;
  hashBase64: string;
};

export type VerifyRequest = {
  password: string;
  record: string;
};

export type VerifyResponse = {
  ok: boolean;
  reason?: string;
};

export type HashBatchSummary = {
  count: number;
  outputBytes: number;
  digestXor: number;
};

export type DemoPacketOptions = {
  count: number;
  iterations?: number;
  keyBytes?: number;
  saltBytes?: number;
};

type ParsedRecord = {
  algorithm: "pbkdf2-sha256";
  iterations: number;
  keyBytes: number;
  salt: Uint8Array;
  hash: Uint8Array;
};

function clampInt(
  value: unknown,
  fallback: number,
  min: number,
  max: number,
): number {
  const numeric = Number(value);
  if (!Number.isFinite(numeric)) return fallback;
  const integer = Math.floor(numeric);
  if (integer < min) return min;
  if (integer > max) return max;
  return integer;
}

function bytesToBase64(bytes: Uint8Array): string {
  let raw = "";
  for (let i = 0; i < bytes.length; i++) raw += String.fromCharCode(bytes[i]!);
  return btoa(raw);
}

function base64ToBytes(value: string): Uint8Array | null {
  try {
    const raw = atob(value);
    const bytes = new Uint8Array(raw.length);
    for (let i = 0; i < raw.length; i++) bytes[i] = raw.charCodeAt(i);
    return bytes;
  } catch {
    return null;
  }
}

function fixedTimeEqual(a: Uint8Array, b: Uint8Array): boolean {
  if (a.length !== b.length) return false;
  let diff = 0;
  for (let i = 0; i < a.length; i++) diff |= a[i]! ^ b[i]!;
  return diff === 0;
}

function assertPassword(password: string): string {
  if (typeof password !== "string" || password.length < 8) {
    throw new Error("password must be at least 8 characters");
  }
  return password;
}

function normalizeSalt(
  saltBase64: string | undefined,
  saltBytes: number,
): Uint8Array {
  if (!saltBase64) return crypto.getRandomValues(new Uint8Array(saltBytes));
  const salt = base64ToBytes(saltBase64);
  if (!salt) throw new Error("saltBase64 is not valid base64");
  if (salt.length < MIN_SALT_BYTES || salt.length > MAX_SALT_BYTES) {
    throw new Error(
      `salt length must be ${MIN_SALT_BYTES}-${MAX_SALT_BYTES} bytes`,
    );
  }
  return salt;
}

async function derivePbkdf2(
  passwordBytes: Uint8Array,
  saltBytes: Uint8Array,
  iterations: number,
  keyBytes: number,
): Promise<Uint8Array> {
  const key = await crypto.subtle.importKey(
    "raw",
    passwordBytes,
    "PBKDF2",
    false,
    ["deriveBits"],
  );

  const bits = await crypto.subtle.deriveBits(
    { name: "PBKDF2", hash: "SHA-256", salt: saltBytes, iterations },
    key,
    keyBytes * 8,
  );

  return new Uint8Array(bits);
}

function makeRecord(
  iterations: number,
  keyBytes: number,
  salt: Uint8Array,
  hash: Uint8Array,
): string {
  return [
    "pbkdf2-sha256",
    String(iterations),
    String(keyBytes),
    bytesToBase64(salt),
    bytesToBase64(hash),
  ].join("$");
}

function parseRecord(record: string): ParsedRecord | null {
  const parts = record.split("$");
  if (parts.length !== 5) return null;
  if (parts[0] !== "pbkdf2-sha256") return null;

  const iterations = Number(parts[1]);
  const keyBytes = Number(parts[2]);
  if (!Number.isInteger(iterations) || !Number.isInteger(keyBytes)) return null;
  if (iterations < MIN_ITERATIONS || iterations > MAX_ITERATIONS) return null;
  if (keyBytes < MIN_KEY_BYTES || keyBytes > MAX_KEY_BYTES) return null;

  const salt = base64ToBytes(parts[3]!);
  const hash = base64ToBytes(parts[4]!);
  if (!salt || !hash) return null;
  if (salt.length < MIN_SALT_BYTES || salt.length > MAX_SALT_BYTES) return null;
  if (hash.length !== keyBytes) return null;

  return {
    algorithm: "pbkdf2-sha256",
    iterations,
    keyBytes,
    salt,
    hash,
  };
}

export async function hashPasswordHost(
  request: HashRequest,
): Promise<HashResponse> {
  const password = assertPassword(request.password);
  const iterations = clampInt(
    request.iterations,
    DEFAULT_ITERATIONS,
    MIN_ITERATIONS,
    MAX_ITERATIONS,
  );
  const keyBytes = clampInt(
    request.keyBytes,
    DEFAULT_KEY_BYTES,
    MIN_KEY_BYTES,
    MAX_KEY_BYTES,
  );
  const saltBytes = clampInt(
    DEFAULT_SALT_BYTES,
    DEFAULT_SALT_BYTES,
    MIN_SALT_BYTES,
    MAX_SALT_BYTES,
  );
  const salt = normalizeSalt(request.saltBase64, saltBytes);

  const hash = await derivePbkdf2(
    encoder.encode(password),
    salt,
    iterations,
    keyBytes,
  );
  const saltBase64 = bytesToBase64(salt);
  const hashBase64 = bytesToBase64(hash);

  return {
    record: makeRecord(iterations, keyBytes, salt, hash),
    algorithm: "pbkdf2-sha256",
    iterations,
    keyBytes,
    saltBase64,
    hashBase64,
  };
}

export async function verifyPasswordHost(
  request: VerifyRequest,
): Promise<VerifyResponse> {
  const password = assertPassword(request.password);
  const parsed = parseRecord(request.record);
  if (!parsed) return { ok: false, reason: "record format is invalid" };

  const hash = await derivePbkdf2(
    encoder.encode(password),
    parsed.salt,
    parsed.iterations,
    parsed.keyBytes,
  );

  return fixedTimeEqual(hash, parsed.hash)
    ? { ok: true }
    : { ok: false, reason: "password mismatch" };
}

export const hashPassword = task<HashRequest, HashResponse>({
  f: hashPasswordHost,
});

export const verifyPassword = task<VerifyRequest, VerifyResponse>({
  f: verifyPasswordHost,
});

function writeU16LE(out: Uint8Array, offset: number, value: number): void {
  out[offset] = value & 255;
  out[offset + 1] = (value >>> 8) & 255;
}

function writeU32LE(out: Uint8Array, offset: number, value: number): void {
  out[offset] = value & 255;
  out[offset + 1] = (value >>> 8) & 255;
  out[offset + 2] = (value >>> 16) & 255;
  out[offset + 3] = (value >>> 24) & 255;
}

function readU16LE(input: Uint8Array, offset: number): number {
  return input[offset]! | (input[offset + 1]! << 8);
}

function readU32LE(input: Uint8Array, offset: number): number {
  return (
    input[offset]! |
    (input[offset + 1]! << 8) |
    (input[offset + 2]! << 16) |
    (input[offset + 3]! << 24)
  ) >>> 0;
}

function toBytes(value: unknown): Uint8Array {
  if (value instanceof Uint8Array) return value;
  if (value instanceof ArrayBuffer) return new Uint8Array(value);
  if (ArrayBuffer.isView(value)) {
    return new Uint8Array(value.buffer, value.byteOffset, value.byteLength);
  }
  if (Array.isArray(value)) {
    const out = new Uint8Array(value.length);
    for (let i = 0; i < value.length; i++) out[i] = Number(value[i] ?? 0) & 255;
    return out;
  }

  if (typeof value !== "object" || value === null) {
    throw new Error("packet is not a byte buffer");
  }

  const candidate = value as {
    length?: unknown;
    byteLength?: unknown;
    data?: unknown;
    [index: number]: unknown;
    [key: string]: unknown;
  };

  if (Array.isArray(candidate.data)) {
    const out = new Uint8Array(candidate.data.length);
    for (let i = 0; i < candidate.data.length; i++) {
      out[i] = Number(candidate.data[i] ?? 0) & 255;
    }
    return out;
  }

  const lengthValue = Number(candidate.length);
  const byteLengthValue = Number(candidate.byteLength);
  let size = Number.isFinite(lengthValue)
    ? Math.max(0, Math.floor(lengthValue))
    : Number.isFinite(byteLengthValue)
    ? Math.max(0, Math.floor(byteLengthValue))
    : -1;

  if (size < 0) {
    let maxIndex = -1;
    for (const key of Object.keys(candidate)) {
      if (/^\d+$/.test(key)) maxIndex = Math.max(maxIndex, Number(key));
    }
    if (maxIndex >= 0) size = maxIndex + 1;
  }

  if (size < 0) throw new Error("packet has no length");

  const out = new Uint8Array(size);
  for (let i = 0; i < size; i++) {
    out[i] = Number(candidate[i] ?? 0) & 255;
  }
  return out;
}

// Compact binary payloads are faster than structured objects for hot loops.
// Header: u16 passwordLen, u16 saltLen, u32 iterations, u16 keyBytes.
export function encodeHashPacket(
  passwordBytes: Uint8Array,
  saltBytes: Uint8Array,
  iterations: number,
  keyBytes: number,
): Uint8Array {
  const headerSize = 10;
  const out = new Uint8Array(
    headerSize + passwordBytes.length + saltBytes.length,
  );
  writeU16LE(out, 0, passwordBytes.length);
  writeU16LE(out, 2, saltBytes.length);
  writeU32LE(out, 4, iterations);
  writeU16LE(out, 8, keyBytes);
  out.set(passwordBytes, headerSize);
  out.set(saltBytes, headerSize + passwordBytes.length);
  return out;
}

function decodeHashPacket(packetLike: unknown): {
  password: Uint8Array;
  salt: Uint8Array;
  iterations: number;
  keyBytes: number;
} {
  const packet = toBytes(packetLike);
  if (packet.length < 10) throw new Error("packet too small");
  const passwordLen = readU16LE(packet, 0);
  const saltLen = readU16LE(packet, 2);
  const iterations = readU32LE(packet, 4);
  const keyBytes = readU16LE(packet, 8);
  const expected = 10 + passwordLen + saltLen;
  if (expected !== packet.length) throw new Error("packet size mismatch");
  if (passwordLen < 8) throw new Error("password too short");
  if (saltLen < MIN_SALT_BYTES || saltLen > MAX_SALT_BYTES) {
    throw new Error("salt size invalid");
  }
  if (iterations < MIN_ITERATIONS || iterations > MAX_ITERATIONS) {
    throw new Error("iterations invalid");
  }
  if (keyBytes < MIN_KEY_BYTES || keyBytes > MAX_KEY_BYTES) {
    throw new Error("key size invalid");
  }

  const password = packet.slice(10, 10 + passwordLen);
  const salt = packet.slice(10 + passwordLen, expected);
  return { password, salt, iterations, keyBytes };
}

// Result packet: u16 saltLen, u16 hashLen, u32 iterations, then salt + hash.
function encodeHashResultPacket(
  salt: Uint8Array,
  hash: Uint8Array,
  iterations: number,
): Uint8Array {
  const out = new Uint8Array(8 + salt.length + hash.length);
  writeU16LE(out, 0, salt.length);
  writeU16LE(out, 2, hash.length);
  writeU32LE(out, 4, iterations);
  out.set(salt, 8);
  out.set(hash, 8 + salt.length);
  return out;
}

export function decodeHashResultPacket(packet: Uint8Array): {
  iterations: number;
  saltBase64: string;
  hashBase64: string;
} {
  if (packet.length < 8) throw new Error("result packet too small");
  const saltLen = readU16LE(packet, 0);
  const hashLen = readU16LE(packet, 2);
  const iterations = readU32LE(packet, 4);
  const expected = 8 + saltLen + hashLen;
  if (expected !== packet.length) {
    throw new Error("result packet size mismatch");
  }

  const salt = packet.slice(8, 8 + saltLen);
  const hash = packet.slice(8 + saltLen, expected);
  return {
    iterations,
    saltBase64: bytesToBase64(salt),
    hashBase64: bytesToBase64(hash),
  };
}

export async function hashPasswordPacketHost(
  packet: Uint8Array,
): Promise<Uint8Array> {
  const decoded = decodeHashPacket(packet);
  const hash = await derivePbkdf2(
    decoded.password,
    decoded.salt,
    decoded.iterations,
    decoded.keyBytes,
  );
  return encodeHashResultPacket(decoded.salt, hash, decoded.iterations);
}

export const hashPasswordPacket = task<Uint8Array, Uint8Array>({
  f: hashPasswordPacketHost,
});

export async function hashPasswordPacketBatchFastHost(
  packets: Uint8Array[],
): Promise<HashBatchSummary> {
  let outputBytes = 0;
  let digestXor = 0;

  for (let i = 0; i < packets.length; i++) {
    const hashed = await hashPasswordPacketHost(packets[i]!);
    outputBytes += hashed.length;
    digestXor ^= hashed[hashed.length - 1] ?? 0;
  }

  return { count: packets.length, outputBytes, digestXor };
}

export const hashPasswordPacketBatchFast = task<Uint8Array[], HashBatchSummary>(
  {
    f: hashPasswordPacketBatchFastHost,
  },
);

function fillDeterministicSalt(seed: number, bytes: number): Uint8Array {
  let x = (seed ^ 0x9e3779b9) >>> 0;
  const out = new Uint8Array(bytes);
  for (let i = 0; i < bytes; i++) {
    x ^= x << 13;
    x ^= x >>> 17;
    x ^= x << 5;
    out[i] = x & 255;
  }
  return out;
}

export function makePasswordBytes(i: number): Uint8Array {
  return encoder.encode(`password-${i.toString(36)}-knitting`);
}

export function makeHashPacketForIndex(
  i: number,
  iterations: number,
  keyBytes: number,
  saltBytes: number,
): Uint8Array {
  const password = makePasswordBytes(i);
  const salt = fillDeterministicSalt(i + 1, saltBytes);
  return encodeHashPacket(password, salt, iterations, keyBytes);
}

export function buildDemoHashPackets(options: DemoPacketOptions): Uint8Array[] {
  const count = clampInt(options.count, 1, 1, 2_000_000);
  const iterations = clampInt(
    options.iterations,
    DEFAULT_ITERATIONS,
    MIN_ITERATIONS,
    MAX_ITERATIONS,
  );
  const keyBytes = clampInt(
    options.keyBytes,
    DEFAULT_KEY_BYTES,
    MIN_KEY_BYTES,
    MAX_KEY_BYTES,
  );
  const saltBytes = clampInt(
    options.saltBytes,
    DEFAULT_SALT_BYTES,
    MIN_SALT_BYTES,
    MAX_SALT_BYTES,
  );

  const packets = new Array<Uint8Array>(count);
  for (let i = 0; i < count; i++) {
    packets[i] = makeHashPacketForIndex(i, iterations, keyBytes, saltBytes);
  }
  return packets;
}

export function hashSummaryFromOutputs(
  outputs: Uint8Array[],
): HashBatchSummary {
  let outputBytes = 0;
  let digestXor = 0;
  for (let i = 0; i < outputs.length; i++) {
    const out = outputs[i]!;
    outputBytes += out.length;
    digestXor ^= out[out.length - 1] ?? 0;
  }
  return { count: outputs.length, outputBytes, digestXor };
}

export function utf8(bytes: Uint8Array): string {
  return decoder.decode(bytes);
}
