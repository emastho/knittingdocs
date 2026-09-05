import { createPool, isMain } from "knitting";
import { bench, boxplot, run, summary } from "mitata";
import { renderUserCard, renderUserCardHost } from "./render_user_card.tsx";
import { buildUserPayloads } from "./utils.ts";

// Sized from measurement, not from core count. One worker is the one setting
// that loses: the transport is not free, and a single lane cannot outrun the
// host it is competing with. Several workers also let the pool use its default
// shared-submit work stealing, which a one-worker pool never engages.
const THREADS = 4;
const REQUESTS = 2_000;

async function main() {
  const payloads = buildUserPayloads(REQUESTS);
  using pool = createPool({ threads: THREADS })({ renderUserCard });
  let sink = 0;

  const hostBytes = runHost(payloads);
  const workerBytes = await runWorkers(pool.call.renderUserCard, payloads);
  console.log(
    `byte parity check: host=${hostBytes.toLocaleString()} ` +
      `worker=${workerBytes.toLocaleString()} ` +
      (hostBytes === workerBytes ? "OK match" : "MISMATCH"),
  );
  if (hostBytes !== workerBytes) {
    throw new Error("Host and worker HTML byte totals differ.");
  }

  console.log("\nReact SSR benchmark (mitata)");
  console.log("workload: parse + normalize + render to HTML");
  console.log("requests per iteration:", REQUESTS.toLocaleString());
  console.log("threads:", THREADS, "\n");

  boxplot(() => {
    summary(() => {
      bench(`host (${REQUESTS.toLocaleString()} req)`, () => {
        sink = runHost(payloads);
      });

      bench(
        `knitting (${THREADS} threads, ${REQUESTS.toLocaleString()} req)`,
        async () => {
          sink = await runWorkers(pool.call.renderUserCard, payloads);
        },
      );
    });
  });

  await run();
  console.log("last html bytes:", sink.toLocaleString());
}

function runHost(payloads: string[]): number {
  let htmlBytes = 0;
  for (let i = 0; i < payloads.length; i++) {
    htmlBytes += renderUserCardHost(payloads[i]!).length;
  }
  return htmlBytes;
}

async function runWorkers(
  callRender: (payload: string) => Promise<string>,
  payloads: string[],
): Promise<number> {
  const jobs: Promise<string>[] = new Array(payloads.length);
  for (let i = 0; i < payloads.length; i++) {
    jobs[i] = callRender(payloads[i]!);
  }

  const results = await Promise.all(jobs);
  let htmlBytes = 0;
  for (let i = 0; i < results.length; i++) htmlBytes += results[i]!.length;
  return htmlBytes;
}

if (isMain) {
  main().catch((error) => {
    console.error(error);
    process.exitCode = 1;
  });
}
