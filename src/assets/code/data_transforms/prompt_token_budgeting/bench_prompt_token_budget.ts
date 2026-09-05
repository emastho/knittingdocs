import { createPool, isMain } from "knitting";
import { bench, boxplot, run, summary } from "mitata";
import { batched, buildPromptInputs } from "./prompt_fixtures.ts";
import {
  mergeSummaries,
  type PromptBudgetSummary,
  type PromptInput,
  summarizeBatch,
  summarizeBatchHost,
} from "./token_budget.ts";

const REQUESTS = 1_000;
const MAX_INPUT_TOKENS = 400;

// Three, not eight. Tokenizing does not scale the way plain compute does --
// read "Why more workers make this slower" on the docs page before raising it. The inliner
// earns its place here: it measured faster than a fourth worker.
const THREADS = 3;

// Batch so there are many more batches than lanes. One batch per lane cannot
// rebalance, and the slowest batch then holds up the whole round.
const BATCH = 32;

async function main() {
  const inputs = buildPromptInputs(REQUESTS, MAX_INPUT_TOKENS);
  const batches = batched(inputs, BATCH);
  using pool = createPool({
    threads: THREADS,
    inliner: { batchSize: 8 },
  })({ summarizeBatch });
  const callBatch = pool.call.summarizeBatch;

  const hostTotals = runHost(batches);
  const workerTotals = await runWorkers(callBatch, batches);
  const parity = hostTotals.budgetedTokens === workerTotals.budgetedTokens &&
    hostTotals.trimmedRuns === workerTotals.trimmedRuns;
  console.log(
    `token parity check: host=${hostTotals.budgetedTokens.toLocaleString()} ` +
      `worker=${workerTotals.budgetedTokens.toLocaleString()} ` +
      (parity ? "OK match" : "MISMATCH"),
  );
  if (!parity) throw new Error("Host and worker budget totals differ.");

  const saved = hostTotals.rawTokens - hostTotals.budgetedTokens;
  console.log("\nPrompt token budgeting benchmark (mitata)");
  console.log("workload: build prompt + tokenize + trim to budget");
  console.log("requests per iteration:", REQUESTS.toLocaleString());
  console.log("budget:", MAX_INPUT_TOKENS, "tokens");
  console.log(
    "trimmed:",
    `${hostTotals.trimmedRuns.toLocaleString()} requests, ` +
      `${((saved / hostTotals.rawTokens) * 100).toFixed(1)}% of tokens saved`,
  );
  console.log("threads:", THREADS, "| batch:", BATCH, "\n");

  let sink = 0;
  boxplot(() => {
    summary(() => {
      bench(`host (${REQUESTS.toLocaleString()} req)`, () => {
        sink = runHost(batches).budgetedTokens;
      });

      bench(
        `knitting (${THREADS} threads, ${REQUESTS.toLocaleString()} req)`,
        async () => {
          sink = (await runWorkers(callBatch, batches)).budgetedTokens;
        },
      );
    });
  });

  await run();
  console.log("last budgeted tokens:", sink.toLocaleString());
}

function runHost(batches: PromptInput[][]): PromptBudgetSummary {
  return mergeSummaries(batches.map(summarizeBatchHost));
}

async function runWorkers(
  callBatch: (inputs: PromptInput[]) => Promise<PromptBudgetSummary>,
  batches: PromptInput[][],
): Promise<PromptBudgetSummary> {
  return mergeSummaries(await Promise.all(batches.map(callBatch)));
}

if (isMain) {
  main().catch((error) => {
    console.error(error);
    process.exitCode = 1;
  });
}
