import React from "react";
import { renderToString } from "react-dom/server";
import { task } from "@vixeny/knitting";

type Args = string;
type Result = { html: string; bytes: number };

type UserStats = {
  posts: number;
  followers: number;
  following: number;
  likes: number;
};

type UserAlerts = {
  unread: number;
  lastLogin: string;
};

type UserPayload = {
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

type NormalizedUser = Required<UserPayload> & {
  stats: UserStats;
  alerts: UserAlerts;
};

function toNumber(value: unknown, fallback: number): number {
  return Number.isFinite(value) ? Number(value) : fallback;
}

function toStringArray(value: unknown): string[] {
  if (!Array.isArray(value)) return [];
  return value.filter((item): item is string => typeof item === "string");
}

function normalizeUser(payload: unknown): NormalizedUser {
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

function formatJoinDate(value: string): string {
  const date = new Date(value);
  if (Number.isNaN(date.getTime())) return value;
  return date.toLocaleDateString("en-US", { month: "short", year: "numeric" });
}

function initials(name: string): string {
  const parts = name.trim().split(/\s+/);
  const first = parts[0]?.[0] ?? "U";
  const second = parts.length > 1 ? parts[1]?.[0] ?? "" : "";
  return (first + second).toUpperCase();
}

function clamp(value: number, min: number, max: number): number {
  return Math.min(max, Math.max(min, value));
}

function engagementScore(stats: UserStats): number {
  return Math.round(
    stats.posts * 2 +
      stats.likes * 0.05 +
      stats.followers * 0.4 +
      stats.following * 0.1,
  );
}

function levelForScore(score: number): string {
  if (score >= 5000) return "Legend";
  if (score >= 2500) return "Elite";
  if (score >= 1000) return "Rising";
  if (score >= 300) return "Active";
  return "New";
}

function Stat({ label, value }: { label: string; value: number }) {
  return (
    <div className="stat">
      <span className="stat-value">{value.toLocaleString()}</span>
      <span className="stat-label">{label}</span>
    </div>
  );
}

function Badge({ plan }: { plan: "free" | "pro" }) {
  const text = plan === "pro" ? "PRO" : "FREE";
  return <span className={`badge badge-${plan}`}>{text}</span>;
}

function UserCard({ user }: { user: NormalizedUser }) {
  const score = engagementScore(user.stats);
  const level = levelForScore(score);
  const joined = formatJoinDate(user.joinedAt);
  const profileCompleteness = (user.bio ? 30 : 0) +
    (user.location ? 20 : 0) +
    (user.tags.length ? 20 : 0) +
    (user.handle ? 10 : 0) +
    (user.stats.posts ? 20 : 0);
  const completeness = clamp(profileCompleteness, 10, 100);
  const topTags = user.tags.slice(0, 6);
  const achievementBadges = [
    user.stats.followers >= 1000 ? "1k+ followers" : "",
    user.stats.likes >= 5000 ? "5k+ likes" : "",
    user.stats.posts >= 50 ? "50+ posts" : "",
  ].filter(Boolean);

  return (
    <article className="user-card" data-user-id={user.id}>
      <header className="user-header">
        <div className="avatar" aria-hidden="true">
          {initials(user.name)}
        </div>
        <div className="meta">
          <div className="title-row">
            <h2>{user.name}</h2>
            <Badge plan={user.plan} />
          </div>
          <div className="handle">{user.handle}</div>
          <div className="subline">
            <span>📍 {user.location}</span>
            <span>• Joined {joined}</span>
          </div>
          <div className="level">
            <span className="pill">Level: {level}</span>
            <span className="pill subtle">Score {score.toLocaleString()}</span>
          </div>
        </div>
        <div className="alerts">
          <span className="pill">{user.alerts.unread} unread</span>
          <span className="pill subtle">
            Last login {user.alerts.lastLogin}
          </span>
        </div>
      </header>

      <section className="bio">
        <h3>Bio</h3>
        {user.bio ? <p>{user.bio}</p> : <p className="muted">No bio yet.</p>}
      </section>

      <section className="profile-complete">
        <h3>Profile completeness</h3>
        <div className="progress">
          <div
            className="progress-bar"
            style={{ width: `${completeness}%` }}
            aria-label={`Profile completeness ${completeness}%`}
          />
        </div>
        <div className="muted">{completeness}% complete</div>
      </section>

      <section className="stats-grid" aria-label="User stats">
        <Stat label="Posts" value={user.stats.posts} />
        <Stat label="Followers" value={user.stats.followers} />
        <Stat label="Following" value={user.stats.following} />
        <Stat label="Likes" value={user.stats.likes} />
      </section>

      <section className="achievements">
        <h3>Highlights</h3>
        <ul>
          {achievementBadges.length > 0
            ? (
              achievementBadges.map((badge) => (
                <li key={badge} className="tag">
                  {badge}
                </li>
              ))
            )
            : <li className="tag muted">Getting started</li>}
        </ul>
      </section>

      <section className="tags">
        <h3>Interests</h3>
        <ul>
          {topTags.length > 0
            ? (
              topTags.map((tag) => (
                <li key={tag} className="tag">
                  {tag}
                </li>
              ))
            )
            : <li className="tag muted">No tags</li>}
        </ul>
      </section>

      <footer className="actions">
        <button type="button">Follow</button>
        <button type="button">Message</button>
        <button type="button" className="ghost">
          View profile
        </button>
      </footer>
    </article>
  );
}

export function renderUserCardHost(payloadJson: string): Result {
  const parsed = JSON.parse(payloadJson) as unknown;
  const user = normalizeUser(parsed);
  const html = renderToString(<UserCard user={user} />);
  return { html, bytes: html.length };
}

export const renderUserCard = task<Args, Result>({
  f: (payloadJson) => {
    return renderUserCardHost(payloadJson);
  },
});
