import React from "react";
import { renderToString } from "react-dom/server";
import { task } from "@vixeny/knitting";
import {
  clamp,
  engagementScore,
  formatJoinDate,
  initials,
  levelForScore,
  type NormalizedUser,
  normalizeUser,
} from "./utils.ts";

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

export function renderUserCardHost(payloadJson: string): string {
  const parsed = JSON.parse(payloadJson) as unknown;
  const user = normalizeUser(parsed);
  const html = renderToString(<UserCard user={user} />);
  return html;
}

export const renderUserCard = task({
  f: renderUserCardHost,
});
