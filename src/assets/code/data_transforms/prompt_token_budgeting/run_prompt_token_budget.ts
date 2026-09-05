import { createPool, isMain } from "knitting";
import { buildPromptInputs } from "./prompt_fixtures.ts";
import { preparePrompt } from "./token_budget.ts";

// A budget only teaches you anything when it actually bites. These
// conversations run roughly 200-1,450 tokens, so 400 trims about half of them.
const REQUESTS = 2_000;
const MAX_INPUT_TOKENS = 400;
const THREADS = 3;

async function main() {
  const inputs = buildPromptInputs(REQUESTS, MAX_INPUT_TOKENS);
  using pool = createPool({ threads: THREADS })({ preparePrompt });

  const started = performance.now();
  const plans = await Promise.all(inputs.map(pool.call.preparePrompt));
  const elapsedMs = performance.now() - started;

  let rawTokens = 0;
  let budgetedTokens = 0;
  let trimmedRuns = 0;
  let queryTrimmedRuns = 0;
  let turnsDropped = 0;

  for (const plan of plans) {
    rawTokens += plan.rawInputTokens;
    budgetedTokens += plan.inputTokens;
    turnsDropped += plan.trimmedTurns;
    if (plan.trimmedTurns > 0) trimmedRuns++;
    if (plan.queryWasTrimmed) queryTrimmedRuns++;
  }

  const saved = rawTokens - budgetedTokens;
  const pct = (part: number) => `${((part / rawTokens) * 100).toFixed(1)}%`;

  console.log("Prompt token budgeting");
  console.log("  requests         :", REQUESTS.toLocaleString());
  console.log("  budget           :", MAX_INPUT_TOKENS, "tokens per prompt");
  console.log("  raw tokens       :", rawTokens.toLocaleString());
  console.log("  budgeted tokens  :", budgetedTokens.toLocaleString());
  console.log(
    "  saved            :",
    `${saved.toLocaleString()} (${pct(saved)})`,
  );
  console.log(
    "  trimmed          :",
    `${trimmedRuns.toLocaleString()} / ${REQUESTS.toLocaleString()} requests`,
  );
  console.log("  turns dropped    :", turnsDropped.toLocaleString());
  console.log("  query clipped    :", queryTrimmedRuns.toLocaleString());
  console.log("  elapsed          :", `${elapsedMs.toFixed(0)} ms`);

  // Every plan carries the bookkeeping needed to explain the decision.
  const example = plans.find((plan) => plan.queryWasTrimmed) ?? plans[0]!;
  console.log("\nOne request, in detail:");
  console.log(`  ${example.rawInputTokens} -> ${example.inputTokens} tokens`);
  console.log(`  ${example.trimmedTurns} turns dropped`);
  console.log(`  query clipped: ${example.queryWasTrimmed}`);
  console.log(`  ${example.staticTokens} of those tokens are the fixed prefix`);
}

if (isMain) {
  main().catch((error) => {
    console.error(error);
    process.exitCode = 1;
  });
}
