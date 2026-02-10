import { createPool, isMain } from "@vixeny/knitting";
import {
  intArg,
  renderUserCard,
  renderUserCardHost,
  strArg,
} from "./render_user_card.tsx";

const THREADS = intArg("threads", 1);
const REQUESTS = intArg("requests", 1000);
const MODE = strArg("mode", "knitting");

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

function makePayload(i: number): string {
  // Pretend this is a user payload arriving over the network.
  // Use JSON strings here to show the “parse → validate → transform” path.
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

async function main() {
  const started = performance.now();
  let finished = started;
  const payloads = new Array<string>(REQUESTS);
  for (let i = 0; i < REQUESTS; i++) payloads[i] = makePayload(i);

  if (MODE === "host") {
    // Baseline: do all parsing + SSR on the host thread.
    for (let i = 0; i < payloads.length; i++) {
      renderUserCardHost(payloads[i]!);
    }
    finished = performance.now();
  } else {
    const pool = createPool({
      threads: THREADS,
    })({ renderUserCard });

    try {
      const jobs: ReturnType<typeof pool.call.renderUserCard>[] = [];

      for (let i = 0; i < payloads.length; i++) {
        jobs.push(pool.call.renderUserCard(payloads[i]));
      }

      await Promise.all(jobs);
      finished = performance.now();
    } finally {
      pool.shutdown();
    }
  }

  const secs = Math.max(1e-9, (finished - started) / 1000);
  const rps = REQUESTS / secs;

  console.log("Worker parsing + SSR-style rendering");
  console.log("mode      :", MODE);
  console.log("threads   :", MODE === "host" ? 0 : THREADS);
  console.log("requests  :", REQUESTS.toLocaleString());
  console.log("took      :", (finished - started).toFixed(2), "ms");
  console.log("throughput:", rps.toFixed(0), "req/s");
}

if (isMain) {
  main().catch((error) => {
    console.error(error);
    process.exitCode = 1;
  });
}
