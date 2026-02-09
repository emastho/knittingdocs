import { createPool, isMain } from "@vixeny/knitting";
import {
  preparePrompt,
  preparePromptHost,
  type PromptInput,
  type PromptPlan,
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
const REQUESTS = Math.max(1, intArg("requests", 20_000));
const MAX_INPUT_TOKENS = Math.max(64, intArg("maxInputTokens", 900));
const MODE = strArg("mode", "knitting");
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
    history[t] = `Need guidance on ${topic}. Include practical steps and one small code example.`;
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

type Totals = {
  rawTokens: number;
  budgetedTokens: number;
  staticTokens: number;
  dynamicTokens: number;
  trimmedRuns: number;
  queryTrimmedRuns: number;
  turnsDropped: number;
};

function summarize(plans: PromptPlan[]): Totals {
  let totals: Totals = {
    rawTokens: 0,
    budgetedTokens: 0,
    staticTokens: 0,
    dynamicTokens: 0,
    trimmedRuns: 0,
    queryTrimmedRuns: 0,
    turnsDropped: 0,
  };

  for (const plan of plans) {
    totals.rawTokens += plan.rawInputTokens;
    totals.budgetedTokens += plan.inputTokens;
    totals.staticTokens += plan.staticTokens;
    totals.dynamicTokens += plan.dynamicTokens;
    totals.turnsDropped += plan.trimmedTurns;
    if (plan.trimmedTurns > 0) totals.trimmedRuns++;
    if (plan.queryWasTrimmed) totals.queryTrimmedRuns++;
  }

  return totals;
}

function runHost(inputs: PromptInput[]): Totals {
  const plans = inputs.map((input) => preparePromptHost(input));
  return summarize(plans);
}

async function runWorkers(inputs: PromptInput[]): Promise<Totals> {
  const pool = createPool({ threads: THREADS })({ preparePrompt });
  try {
    const jobs: Promise<PromptPlan>[] = [];
    for (let i = 0; i < inputs.length; i++) {
      jobs.push(pool.call.preparePrompt(inputs[i]!));
    }

    pool.send();
    const plans = await Promise.all(jobs);
    return summarize(plans);
  } finally {
    pool.shutdown();
  }
}

function percent(saved: number, base: number): string {
  if (base <= 0) return "0.0%";
  return `${((saved / base) * 100).toFixed(1)}%`;
}

async function main() {
  const inputs = new Array<PromptInput>(REQUESTS);
  for (let i = 0; i < REQUESTS; i++) inputs[i] = makeInput(i);

  const started = performance.now();
  const totals = MODE === "host"
    ? runHost(inputs)
    : await runWorkers(inputs);
  const finished = performance.now();

  const tookMs = finished - started;
  const secs = Math.max(1e-9, tookMs / 1000);
  const reqPerSec = REQUESTS / secs;
  const savedTokens = Math.max(0, totals.rawTokens - totals.budgetedTokens);
  const cacheableTokensEstimate = totals.staticTokens;

  console.log("Prompt token budgeting");
  console.log("mode              :", MODE);
  console.log("model             :", MODEL);
  console.log("threads           :", MODE === "host" ? 0 : THREADS);
  console.log("requests          :", REQUESTS.toLocaleString());
  console.log("maxInputTokens    :", MAX_INPUT_TOKENS.toLocaleString());
  console.log("raw tokens        :", totals.rawTokens.toLocaleString());
  console.log("budgeted tokens   :", totals.budgetedTokens.toLocaleString());
  console.log(
    "saved tokens      :",
    `${savedTokens.toLocaleString()} (${percent(savedTokens, totals.rawTokens)})`,
  );
  console.log("trimmed runs      :", totals.trimmedRuns.toLocaleString());
  console.log("query trimmed runs:", totals.queryTrimmedRuns.toLocaleString());
  console.log("turns dropped     :", totals.turnsDropped.toLocaleString());
  console.log("cacheable estimate:", cacheableTokensEstimate.toLocaleString());
  console.log("took              :", tookMs.toFixed(2), "ms");
  console.log("throughput        :", reqPerSec.toFixed(0), "req/s");
}

if (isMain) {
  main().catch((error) => {
    console.error(error);
    process.exitCode = 1;
  });
}
