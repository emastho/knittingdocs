import { createPool, isMain } from "@vixeny/knitting";
import { renderUserCard, renderUserCardHost } from "./render_user_card.tsx";

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

const THREADS = intArg("threads", 6);
const REQUESTS = intArg("requests", 50_000);
const BATCH = intArg("batch", 64);
const MODE = strArg("mode", "knitting");

function makePayload(i: number): string {
  // Pretend this is a user payload arriving over the network.
  // Use JSON strings here to show the “parse → validate → transform” path.
  const short = i.toString(36);
  const payload = JSON.stringify({
    id: `u${short}`,
    name: `U${short}`,
  });

  // Keep payloads tiny (<= 44 bytes).
  if (payload.length <= 44) return payload;
  return `{"i":"${short}"}`;
}

async function main() {
  const started = performance.now();
  const payloads = new Array<string>(REQUESTS);
  for (let i = 0; i < REQUESTS; i++) payloads[i] = makePayload(i);
  let sampleHtml = "";
  let totalBytes = 0;

  if (MODE === "host") {
    // Baseline: do all parsing + SSR on the host thread.
    for (let i = 0; i < payloads.length; i++) {
      const res = renderUserCardHost(payloads[i]!);
      totalBytes += res.bytes;
      if (i === 0) sampleHtml = res.html;
    }
  } else {
    const pool = createPool({
      threads: THREADS,
    })({ renderUserCard });

    const jobs: Promise<{ html: string; bytes: number }>[] = [];
    for (let i = 0; i < payloads.length; i++) {
      jobs.push(pool.fastCall.renderUserCard([payloads[i]!]));
      if ((i + 1) % BATCH === 0) pool.send();
    }
    pool.send();
    const results = await Promise.all(jobs);
    for (let i = 0; i < results.length; i++) {
      const res = results[i]!;
      totalBytes += res.bytes;
      if (i === 0) sampleHtml = res.html;
    }

    await pool.shutdown();
  }
  const finished = performance.now();


  const secs = Math.max(1e-9, (finished - started) / 1000);
  const rps = REQUESTS / secs;

  console.log("Worker parsing + SSR-style rendering");
  console.log("mode      :", MODE);
  console.log("threads   :", MODE === "host" ? 0 : THREADS);
  console.log("requests  :", REQUESTS.toLocaleString());
  console.log("payload   :", "<= 44 bytes JSON");
  console.log("batch     :", BATCH.toLocaleString());
  console.log("took      :", (finished - started).toFixed(2), "ms");
  console.log("throughput:", rps.toFixed(0), "req/s");
  console.log("output    :", (totalBytes / (1024 * 1024)).toFixed(2), "MiB HTML");
  console.log("---");
  console.log("sample:\n" + sampleHtml);

}

if (isMain) {
  main().catch((err) => {
    console.error(err);
    process.exitCode = 1;
  });
}
