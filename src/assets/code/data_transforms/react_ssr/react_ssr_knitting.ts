import { createPool, isMain } from "@vixeny/knitting";
import { renderUserCard, renderUserCardHost } from "./render_user_card.tsx";

const THREADS = 2;
const REQUESTS = 20_000;

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

function buildPayloads(): string[] {
  const payloads = new Array<string>(REQUESTS);
  for (let i = 0; i < REQUESTS; i++) payloads[i] = makePayload(i);
  return payloads;
}

function printMetrics(mode: string, ms: number, htmlBytes: number): void {
  const secs = Math.max(1e-9, ms / 1000);
  const rps = REQUESTS / secs;
  console.log(mode);
  console.log("requests    :", REQUESTS.toLocaleString());
  console.log("html bytes  :", htmlBytes.toLocaleString());
  console.log("took        :", `${ms.toFixed(2)} ms`);
  console.log("throughput  :", `${rps.toFixed(0)} req/s`);
}

function runHost(payloads: string[]): { ms: number; bytes: number } {
  let htmlBytes = 0;
  const started = performance.now();
  for (let i = 0; i < payloads.length; i++) {
    const result = renderUserCardHost(payloads[i]!);
    htmlBytes += result.bytes;
  }
  return { ms: performance.now() - started, bytes: htmlBytes };
}

async function runWorkers(
  payloads: string[],
): Promise<{ ms: number; bytes: number }> {
  const pool = createPool({ threads: THREADS })({ renderUserCard });
  let htmlBytes = 0;

  try {
    const started = performance.now();
    const jobs: ReturnType<typeof pool.call.renderUserCard>[] = [];
    for (let i = 0; i < payloads.length; i++) {
      jobs.push(pool.call.renderUserCard(payloads[i]!));
    }

    const results = await Promise.all(jobs);
    for (let i = 0; i < results.length; i++) {
      htmlBytes += results[i]!.bytes;
    }
    return { ms: performance.now() - started, bytes: htmlBytes };
  } finally {
    pool.shutdown();
  }
}

async function main() {
  const payloads = buildPayloads();
  const host = runHost(payloads);
  const knitting = await runWorkers(payloads);
  const uplift = (host.ms / Math.max(1e-9, knitting.ms) - 1) * 100;

  console.log("React SSR quick run");
  console.log(`threads: ${THREADS}`);
  console.log("");
  printMetrics("host", host.ms, host.bytes);
  console.log("");
  printMetrics("knitting", knitting.ms, knitting.bytes);
  console.log("");
  console.log(`uplift: ${uplift.toFixed(1)}%`);
}

if (isMain) {
  main().catch((error) => {
    console.error(error);
    process.exitCode = 1;
  });
}
