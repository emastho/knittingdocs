export type UserStats = {
  posts: number;
  followers: number;
  following: number;
  likes: number;
};

export type UserAlerts = {
  unread: number;
  lastLogin: string;
};

export type UserPayload = {
  id?: string;
  name?: string;
  handle?: string;
  bio?: string;
  plan?: "free" | "pro";
  location?: string;
  joinedAt?: string;
  tags?: string[];
  stats?: Partial<UserStats>;
  alerts?: Partial<UserAlerts>;
};

export type NormalizedUser = Required<UserPayload> & {
  stats: UserStats;
  alerts: UserAlerts;
};

const TAGS = [
  "react",
  "ssr",
  "typescript",
  "performance",
  "parallel",
  "workers",
  "ui",
  "web",
];
const LOCATIONS = ["Austin, TX", "Seattle, WA", "Brooklyn, NY", "Denver, CO"];

function pickFrom<T>(arr: T[], index: number): T {
  return arr[index % arr.length]!;
}

function toNumber(value: unknown, fallback: number): number {
  return Number.isFinite(value) ? Number(value) : fallback;
}

function toStringArray(value: unknown): string[] {
  if (!Array.isArray(value)) return [];
  return value.filter((item): item is string => typeof item === "string");
}

export function makeUserPayloadJson(i: number): string {
  const short = i.toString(36);

  return JSON.stringify({
    id: `u${short}`,
    name: `User ${short.toUpperCase()}`,
    handle: `@${short}`,
    bio: `Building fast UIs. Coffee + TypeScript. (${short})`,
    plan: i % 7 === 0 ? "pro" : "free",
    location: pickFrom(LOCATIONS, i),
    joinedAt: `202${(i % 4) + 2}-0${(i % 8) + 1}-1${i % 9}`,
    tags: [
      pickFrom(TAGS, i),
      pickFrom(TAGS, i + 1),
      pickFrom(TAGS, i + 2),
      pickFrom(TAGS, i + 3),
    ],
    stats: {
      posts: (i % 120) + 1,
      followers: (i * 13) % 50_000,
      following: (i * 7) % 5_000,
      likes: (i * 31) % 250_000,
    },
    alerts: {
      unread: i % 25,
      lastLogin: `2026-0${(i % 8) + 1}-0${(i % 9) + 1}`,
    },
  });
}

export function buildUserPayloads(count: number): string[] {
  const payloads = new Array<string>(count);
  for (let i = 0; i < count; i++) payloads[i] = makeUserPayloadJson(i);
  return payloads;
}

export function normalizeUser(payload: unknown): NormalizedUser {
  const obj = (payload ?? {}) as Record<string, unknown>;

  const id = typeof obj.id === "string" ? obj.id : "unknown";
  const name = typeof obj.name === "string" ? obj.name : "Anonymous";
  const handle = typeof obj.handle === "string" ? obj.handle : `@${id}`;
  const bio = typeof obj.bio === "string" ? obj.bio : "";
  const plan = obj.plan === "pro" ? "pro" : "free";
  const location = typeof obj.location === "string" ? obj.location : "Unknown";
  const joinedAt = typeof obj.joinedAt === "string"
    ? obj.joinedAt
    : "2024-05-01";

  const statsRaw = (obj.stats ?? {}) as Record<string, unknown>;
  const alertsRaw = (obj.alerts ?? {}) as Record<string, unknown>;

  const stats: UserStats = {
    posts: toNumber(statsRaw.posts, 0),
    followers: toNumber(statsRaw.followers, 0),
    following: toNumber(statsRaw.following, 0),
    likes: toNumber(statsRaw.likes, 0),
  };

  const alerts: UserAlerts = {
    unread: toNumber(alertsRaw.unread, 0),
    lastLogin: typeof alertsRaw.lastLogin === "string"
      ? alertsRaw.lastLogin
      : "2026-01-18",
  };

  const tags = toStringArray(obj.tags);

  return {
    id,
    name,
    handle,
    bio,
    plan,
    location,
    joinedAt,
    tags,
    stats,
    alerts,
  };
}

export function formatJoinDate(value: string): string {
  const date = new Date(value);
  if (Number.isNaN(date.getTime())) return value;
  return date.toLocaleDateString("en-US", { month: "short", year: "numeric" });
}

export function initials(name: string): string {
  const parts = name.trim().split(/\s+/);
  const first = parts[0]?.[0] ?? "U";
  const second = parts.length > 1 ? parts[1]?.[0] ?? "" : "";
  return (first + second).toUpperCase();
}

export function clamp(value: number, min: number, max: number): number {
  return Math.min(max, Math.max(min, value));
}

export function engagementScore(stats: UserStats): number {
  return Math.round(
    stats.posts * 2 +
      stats.likes * 0.05 +
      stats.followers * 0.4 +
      stats.following * 0.1,
  );
}

export function levelForScore(score: number): string {
  if (score >= 5000) return "Legend";
  if (score >= 2500) return "Elite";
  if (score >= 1000) return "Rising";
  if (score >= 300) return "Active";
  return "New";
}
