import { createPool, isMain } from "@vixeny/knitting";
import { bench, boxplot, run, summary } from "mitata";
import {
  preparePromptBatchFast,
  preparePromptBatchFastHost,
  type PromptBudgetSummary,
  type PromptInput,
} from "./token_budget.ts";

function intArg(name: string, fallback: number): number {
  const i = process.argv.indexOf(`--${name}`);
  if (i !== -1 && i + 1 < process.argv.length) {
    const value = Number(process.argv[i + 1]);
    if (Number.isFinite(value)) return Math.floor(value);
  }
  return fallback;
}

function strArg(name: string, fallback: string): string {
  const i = process.argv.indexOf(`--${name}`);
  if (i !== -1 && i + 1 < process.argv.length) {
    return String(process.argv[i + 1]);
  }
  return fallback;
}

const THREADS = Math.max(1, intArg("threads", 2));
const REQUESTS = Math.max(1, intArg("requests", 10));
const MAX_INPUT_TOKENS = Math.max(64, intArg("maxInputTokens", 500));
const BATCH = Math.max(1, intArg("batch", 32));
const MODEL = strArg("model", "gpt-4o-mini");

const SYSTEM_PREFIX = [
  "You are a docs assistant.",
  "Prefer concrete and short answers.",
  "If data is missing, say it directly.",
  "Do not invent unsupported behavior.",
].join("\n");

const TOPICS = [
  "token budgeting",
  "prompt caching",
  "parallel workers",
  "schema validation",
  "rendering pipelines",
  "markdown output",
  "compression tradeoffs",
  "latency under load",
];

function pick<T>(arr: T[], i: number): T {
  return arr[i % arr.length]!;
}

function makeHistory(i: number): string[] {
  const turns = 3 + (i % 10);
  const history = new Array<string>(turns);

  for (let t = 0; t < turns; t++) {
    const topic = pick(TOPICS, i + t);
    history[t] =
      `Need guidance on ${topic}. Include practical steps and one small code example.`;
  }

  return history;
}

function makeInput(i: number): PromptInput {
  const topicA = pick(TOPICS, i);
  const topicB = pick(TOPICS, i + 3);
  const query = [
    `Please compare ${topicA} with ${topicB}.`,
    "I care about cost per request and response quality.",
    "Give a short recommendation and a migration path.",
  ].join(" ");

  return {
    model: MODEL,
    systemPrefix: SYSTEM_PREFIX,
    history: makeHistory(i),
    query,
    maxInputTokens: MAX_INPUT_TOKENS,
  };
}

function makeBatches<T>(values: T[], batchSize: number): T[][] {
  const batches: T[][] = [];
  for (let i = 0; i < values.length; i += batchSize) {
    batches.push(values.slice(i, i + batchSize));
  }
  return batches;
}

function mergeSummary(
  a: PromptBudgetSummary,
  b: PromptBudgetSummary,
): PromptBudgetSummary {
  return {
    rawTokens: a.rawTokens + b.rawTokens,
    budgetedTokens: a.budgetedTokens + b.budgetedTokens,
    staticTokens: a.staticTokens + b.staticTokens,
    dynamicTokens: a.dynamicTokens + b.dynamicTokens,
    trimmedRuns: a.trimmedRuns + b.trimmedRuns,
    queryTrimmedRuns: a.queryTrimmedRuns + b.queryTrimmedRuns,
    turnsDropped: a.turnsDropped + b.turnsDropped,
  };
}

function runHostBatches(inputBatches: PromptInput[][]): PromptBudgetSummary {
  let totals: PromptBudgetSummary = {
    rawTokens: 0,
    budgetedTokens: 0,
    staticTokens: 0,
    dynamicTokens: 0,
    trimmedRuns: 0,
    queryTrimmedRuns: 0,
    turnsDropped: 0,
  };

  for (let i = 0; i < inputBatches.length; i++) {
    totals = mergeSummary(totals, preparePromptBatchFastHost(inputBatches[i]!));
  }

  return totals;
}

async function runWorkerBatches(
  callBatch: (inputs: PromptInput[]) => Promise<PromptBudgetSummary>,
  inputBatches: PromptInput[][],
): Promise<PromptBudgetSummary> {
  const jobs: Promise<PromptBudgetSummary>[] = [];
  for (let i = 0; i < inputBatches.length; i++) {
    jobs.push(callBatch(inputBatches[i]!));
  }

  const results = await Promise.all(jobs);

  let totals: PromptBudgetSummary = {
    rawTokens: 0,
    budgetedTokens: 0,
    staticTokens: 0,
    dynamicTokens: 0,
    trimmedRuns: 0,
    queryTrimmedRuns: 0,
    turnsDropped: 0,
  };

  for (let i = 0; i < results.length; i++) {
    totals = mergeSummary(totals, results[i]!);
  }

  return totals;
}

function sameSummary(a: PromptBudgetSummary, b: PromptBudgetSummary): boolean {
  return a.rawTokens === b.rawTokens &&
    a.budgetedTokens === b.budgetedTokens &&
    a.staticTokens === b.staticTokens &&
    a.dynamicTokens === b.dynamicTokens &&
    a.trimmedRuns === b.trimmedRuns &&
    a.queryTrimmedRuns === b.queryTrimmedRuns &&
    a.turnsDropped === b.turnsDropped;
}

async function main() {
  const inputs = new Array<PromptInput>(REQUESTS);
  for (let i = 0; i < REQUESTS; i++) {
    inputs[i] = makeInput(i);
  }
  const inputBatches = makeBatches(inputs, BATCH);

  const pool = createPool({
    threads: THREADS - 1,
    inliner: {
      batchSize: 8,
    },
  })({ preparePromptBatchFast });
  let sink = 0;

  try {
    const hostCheck = runHostBatches(inputBatches);
    const workerCheck = await runWorkerBatches(
      pool.call.preparePromptBatchFast,
      inputBatches,
    );
    if (!sameSummary(hostCheck, workerCheck)) {
      throw new Error("Host and worker prompt-budget totals differ.");
    }

    console.log("Prompt token budgeting benchmark (mitata)");
    console.log("workload: build prompt + tokenize + trim to budget");
    console.log("model:", MODEL);
    console.log("requests per iteration:", REQUESTS.toLocaleString());
    console.log("max input tokens:", MAX_INPUT_TOKENS.toLocaleString());
    console.log("batch size:", BATCH);
    console.log("threads:", THREADS);

    boxplot(() => {
      summary(() => {
        bench(`host (${REQUESTS.toLocaleString()} req, batch ${BATCH})`, () => {
          const totals = runHostBatches(inputBatches);
          sink = totals.budgetedTokens;
        });

        bench(
          `knitting (${THREADS} thread${
            THREADS === 1 ? "" : "s"
          }, ${REQUESTS.toLocaleString()} req, batch ${BATCH})`,
          async () => {
            const totals = await runWorkerBatches(
              pool.call.preparePromptBatchFast,
              inputBatches,
            );
            sink = totals.budgetedTokens;
          },
        );
      });
    });

    await run();
    console.log("last budgeted tokens:", sink.toLocaleString());
  } finally {
    pool.shutdown();
  }
}

if (isMain) {
  main().catch((error) => {
    console.error(error);
    process.exitCode = 1;
  });
}
