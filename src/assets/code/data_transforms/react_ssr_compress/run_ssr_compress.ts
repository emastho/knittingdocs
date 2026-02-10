import { createPool, isMain } from "@vixeny/knitting";
import {
  renderUserCard,
  renderUserCardHost,
} from "../react_ssr/render_user_card.tsx";
import { renderUserCardCompressed } from "./render_user_card_compressed.tsx";
import { brotliCompressSync } from "node:zlib";

function intArg(name: string, fallback: number) {
  const i = process.argv.indexOf(`--${name}`);
  if (i !== -1 && i + 1 < process.argv.length) {
    const v = Number(process.argv[i + 1]);
    if (Number.isFinite(v) && v > 0) return Math.floor(v);
  }
  return fallback;
}

function strArg(name: string, fallback: string) {
  const i = process.argv.indexOf(`--${name}`);
  if (i !== -1 && i + 1 < process.argv.length) {
    return String(process.argv[i + 1]);
  }
  return fallback;
}

const THREADS = intArg("threads", 1);
const REQUESTS = intArg("requests", 5000);

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

function compressHtml(html: string) {
  return brotliCompressSync(html);
}

async function main() {
  const started = performance.now();
  const payloads = new Array<string>(REQUESTS);
  for (let i = 0; i < REQUESTS; i++) payloads[i] = makePayload(i);
  let compressedBytes = 0;

  if (MODE === "host") {
    for (let i = 0; i < payloads.length; i++) {
      const res = renderUserCardHost(payloads[i]!);
      compressedBytes += compressHtml(res.html).byteLength;
    }
  } else {
    const pool = createPool({
      threads: THREADS,
      inliner: {
        position: "last",
        batchSize: 8,
        // Keep host lane out at light load; let it help on bursts.
        dispatchThreshold: 16,
      },
    })({ renderUserCard, renderUserCardCompressed });

    try {
      const jobs: ReturnType<typeof pool.call.renderUserCardCompressed>[] = [];
      for (let i = 0; i < payloads.length; i++) {
        jobs.push(pool.call.renderUserCardCompressed(payloads[i]));
      }

      const compressed = await Promise.all(jobs);
      for (const chunk of compressed) compressedBytes += chunk.byteLength;
    } finally {
      pool.shutdown();
    }
  }

  const finished = performance.now();
  const secs = Math.max(1e-9, (finished - started) / 1000);
  const rps = REQUESTS / secs;

  console.log("Worker parsing + SSR + compression");
  console.log("mode        :", MODE);
  console.log("threads     :", MODE === "host" ? 0 : THREADS);
  console.log("requests    :", REQUESTS.toLocaleString());
  console.log("compress    :", "brotli");
  console.log("bytes       :", compressedBytes.toLocaleString());
  console.log("took        :", (finished - started).toFixed(2), "ms");
  console.log("throughput  :", rps.toFixed(0), "req/s");
}

if (isMain) {
  main().catch((err) => {
    console.error(err);
    process.exitCode = 1;
  });
}
