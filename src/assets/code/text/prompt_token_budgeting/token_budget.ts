import { task } from "knitting";
import { encoding_for_model } from "tiktoken";

export type PromptInput = {
  model: string;
  systemPrefix: string;
  history: string[];
  query: string;
  maxInputTokens: number;
};

export type PromptPlan = {
  prompt: string;
  rawInputTokens: number;
  inputTokens: number;
  staticTokens: number;
  dynamicTokens: number;
  trimmedTurns: number;
  queryWasTrimmed: boolean;
};

/** What a batch of plans adds up to. No prompt strings, so it is cheap to return. */
export type PromptBudgetSummary = {
  rawTokens: number;
  budgetedTokens: number;
  staticTokens: number;
  dynamicTokens: number;
  trimmedRuns: number;
  queryTrimmedRuns: number;
  turnsDropped: number;
};

type Encoder = ReturnType<typeof encoding_for_model>;

const decoder = new TextDecoder();
const encoderCache = new Map<string, Encoder>();
const staticTokenCache = new Map<string, number>();

// A tiktoken encoder is a WASM instance holding its own BPE table, and it costs
// tens of megabytes resident. This cache lives per worker, so the real ceiling
// is MAX_ENCODERS * threads. Keep it small, and free whatever you evict.
const MAX_ENCODERS = 2;

function getEncoder(model: string): Encoder {
  const cached = encoderCache.get(model);
  if (cached) return cached;

  const enc = encoding_for_model(model as never);
  encoderCache.set(model, enc);

  if (encoderCache.size > MAX_ENCODERS) {
    const oldest = encoderCache.keys().next().value!;
    encoderCache.get(oldest)!.free();
    encoderCache.delete(oldest);
  }

  return enc;
}

/** The system prefix is identical on every request, so tokenize it once. */
function getStaticTokens(model: string, prefix: string, enc: Encoder): number {
  const key = `${model}\x1f${prefix}`;
  const cached = staticTokenCache.get(key);
  if (cached !== undefined) return cached;

  const value = enc.encode(prefix).length;
  staticTokenCache.set(key, value);
  return value;
}

export function clearPromptBudgetCaches(): void {
  for (const enc of encoderCache.values()) enc.free();
  encoderCache.clear();
  staticTokenCache.clear();
}

function normalizeText(value: string): string {
  return value.replace(/\s+/g, " ").trim();
}

function buildPrompt(prefix: string, history: string[], query: string): string {
  const rows = [prefix.trim(), "", "Conversation context:"];
  for (let i = 0; i < history.length; i++) {
    rows.push(`- Turn ${i + 1}: ${history[i]}`);
  }
  rows.push("", `User request: ${query}`);
  return rows.join("\n");
}

function truncateToTokenBudget(
  enc: Encoder,
  text: string,
  maxTokens: number,
): string {
  if (maxTokens <= 0) return "";

  const tokens = enc.encode(text);
  if (tokens.length <= maxTokens) return text;
  return decoder.decode(enc.decode(tokens.slice(0, maxTokens)));
}

/**
 * Fit a prompt inside `maxInputTokens`: drop the oldest turns first, and only
 * clip the query if dropping every turn still is not enough.
 */
export function preparePromptHost(input: PromptInput): PromptPlan {
  const maxInputTokens = Math.max(64, input.maxInputTokens);
  const history = input.history.map(normalizeText).filter(Boolean);
  const enc = getEncoder(input.model);
  const staticTokens = getStaticTokens(input.model, input.systemPrefix, enc);

  let query = normalizeText(input.query);
  let prompt = buildPrompt(input.systemPrefix, history, query);
  const rawInputTokens = enc.encode(prompt).length;
  let inputTokens = rawInputTokens;
  let trimmedTurns = 0;
  let queryWasTrimmed = false;

  while (inputTokens > maxInputTokens && history.length > 0) {
    history.shift();
    trimmedTurns++;
    prompt = buildPrompt(input.systemPrefix, history, query);
    inputTokens = enc.encode(prompt).length;
  }

  // No turns left to drop and still over: the query itself is the problem.
  if (inputTokens > maxInputTokens) {
    const scaffolding = buildPrompt(input.systemPrefix, history, "");
    const remaining = Math.max(
      16,
      maxInputTokens - enc.encode(scaffolding).length,
    );
    const clipped = truncateToTokenBudget(enc, query, remaining);
    queryWasTrimmed = clipped.length < query.length;
    query = clipped;
    prompt = buildPrompt(input.systemPrefix, history, query);
    inputTokens = enc.encode(prompt).length;
  }

  return {
    prompt,
    rawInputTokens,
    inputTokens,
    staticTokens,
    dynamicTokens: Math.max(0, inputTokens - staticTokens),
    trimmedTurns,
    queryWasTrimmed,
  };
}

/**
 * Budget a whole batch and return only the counters. Batching amortizes the
 * per-call dispatch, and dropping the prompt strings keeps the return small.
 */
export function summarizeBatchHost(
  inputs: PromptInput[],
): PromptBudgetSummary {
  const totals = emptySummary();

  for (let i = 0; i < inputs.length; i++) {
    const plan = preparePromptHost(inputs[i]!);
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

export function emptySummary(): PromptBudgetSummary {
  return {
    rawTokens: 0,
    budgetedTokens: 0,
    staticTokens: 0,
    dynamicTokens: 0,
    trimmedRuns: 0,
    queryTrimmedRuns: 0,
    turnsDropped: 0,
  };
}

export function mergeSummaries(
  parts: PromptBudgetSummary[],
): PromptBudgetSummary {
  return parts.reduce((a, b) => ({
    rawTokens: a.rawTokens + b.rawTokens,
    budgetedTokens: a.budgetedTokens + b.budgetedTokens,
    staticTokens: a.staticTokens + b.staticTokens,
    dynamicTokens: a.dynamicTokens + b.dynamicTokens,
    trimmedRuns: a.trimmedRuns + b.trimmedRuns,
    queryTrimmedRuns: a.queryTrimmedRuns + b.queryTrimmedRuns,
    turnsDropped: a.turnsDropped + b.turnsDropped,
  }), emptySummary());
}

/** Returns the full plan, prompt string included. */
export const preparePrompt = task<PromptInput, PromptPlan>({
  f: preparePromptHost,
});

/** Returns counters only. This is the one worth benchmarking. */
export const summarizeBatch = task<PromptInput[], PromptBudgetSummary>({
  f: summarizeBatchHost,
});
