import { createPool, isMain } from "@vixeny/knitting";
import { bench, boxplot, run, summary } from "mitata";
import {
  buildDemoHashPackets,
  type HashBatchSummary,
  hashPasswordPacketBatchFast,
  hashPasswordPacketBatchFastHost,
} from "./utils.ts";

const THREADS = 2;
const REQUESTS = 500;
const BATCH = 32;
const ITERATIONS = 1_200;
const KEY_BYTES = 32;
const SALT_BYTES = 16;

async function main() {
  const packets = buildDemoHashPackets({
    count: REQUESTS,
    iterations: ITERATIONS,
    keyBytes: KEY_BYTES,
    saltBytes: SALT_BYTES,
  });
  const batches = makeBatches(packets, BATCH);

  const pool = createPool({ threads: THREADS })({
    hashPasswordPacketBatchFast,
  });
  let sink = 0;

  try {
    const hostCheck = await runHostBatches(batches);
    const workerCheck = await runWorkerBatches(
      pool.call.hashPasswordPacketBatchFast,
      batches,
    );

    if (!same(hostCheck, workerCheck)) {
      throw new Error("Host and worker hashing summaries differ.");
    }

    console.log("Salt hashing benchmark (mitata)");
    console.log("workload: PBKDF2-SHA256 on Uint8Array request packets");
    console.log("requests per iteration:", REQUESTS.toLocaleString());
    console.log("iterations:", ITERATIONS.toLocaleString());
    console.log("batch size:", BATCH);
    console.log("threads:", THREADS);

    boxplot(() => {
      summary(() => {
        bench(
          `host (${REQUESTS.toLocaleString()} req, batch ${BATCH})`,
          async () => {
            const totals = await runHostBatches(batches);
            sink = totals.outputBytes ^ totals.digestXor;
          },
        );

        bench(
          `knitting (${THREADS} thread${
            THREADS === 1 ? "" : "s"
          }, ${REQUESTS.toLocaleString()} req, batch ${BATCH})`,
          async () => {
            const totals = await runWorkerBatches(
              pool.call.hashPasswordPacketBatchFast,
              batches,
            );
            sink = totals.outputBytes ^ totals.digestXor;
          },
        );
      });
    });

    await run();
    console.log("last sink:", sink.toLocaleString());
  } finally {
    pool.shutdown();
  }
}

function makeBatches(packets: Uint8Array[], batchSize: number): Uint8Array[][] {
  const out: Uint8Array[][] = [];
  for (let i = 0; i < packets.length; i += batchSize) {
    out.push(packets.slice(i, i + batchSize));
  }
  return out;
}

function merge(a: HashBatchSummary, b: HashBatchSummary): HashBatchSummary {
  return {
    count: a.count + b.count,
    outputBytes: a.outputBytes + b.outputBytes,
    digestXor: a.digestXor ^ b.digestXor,
  };
}

async function runHostBatches(
  batches: Uint8Array[][],
): Promise<HashBatchSummary> {
  let totals: HashBatchSummary = { count: 0, outputBytes: 0, digestXor: 0 };
  for (let i = 0; i < batches.length; i++) {
    totals = merge(totals, await hashPasswordPacketBatchFastHost(batches[i]!));
  }
  return totals;
}

async function runWorkerBatches(
  callBatch: (packets: Uint8Array[]) => Promise<HashBatchSummary>,
  batches: Uint8Array[][],
): Promise<HashBatchSummary> {
  const jobs: Promise<HashBatchSummary>[] = [];
  for (let i = 0; i < batches.length; i++) jobs.push(callBatch(batches[i]!));
  const results = await Promise.all(jobs);

  let totals: HashBatchSummary = { count: 0, outputBytes: 0, digestXor: 0 };
  for (let i = 0; i < results.length; i++) totals = merge(totals, results[i]!);
  return totals;
}

function same(a: HashBatchSummary, b: HashBatchSummary): boolean {
  return a.count === b.count &&
    a.outputBytes === b.outputBytes &&
    a.digestXor === b.digestXor;
}

if (isMain) {
  main().catch((error) => {
    console.error(error);
    process.exitCode = 1;
  });
}
