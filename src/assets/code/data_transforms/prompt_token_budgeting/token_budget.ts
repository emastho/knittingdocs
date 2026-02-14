import { task } from "@vixeny/knitting";
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

export type PromptPlanFast = Omit<PromptPlan, "prompt">;

export type PromptBudgetSummary = {
  rawTokens: number;
  budgetedTokens: number;
  staticTokens: number;
  dynamicTokens: number;
  trimmedRuns: number;
  queryTrimmedRuns: number;
  turnsDropped: number;
};

const decoder = new TextDecoder();
type Encoder = ReturnType<typeof encoding_for_model>;
const MAX_ENCODER_CACHE = 4;
const MAX_STATIC_TOKEN_CACHE = 512;
const encoderCache = new Map<string, Encoder>();
const staticTokenCache = new Map<string, number>();

function normalizeText(value: string): string {
  return value.replace(/\s+/g, " ").trim();
}

function countTokens(enc: Encoder, text: string): number {
  return enc.encode(text).length;
}

function touchMapEntry<V>(map: Map<string, V>, key: string, value: V): void {
  map.delete(key);
  map.set(key, value);
}

function evictOldestEncoderIfNeeded(): void {
  if (encoderCache.size <= MAX_ENCODER_CACHE) return;
  const oldest = encoderCache.keys().next().value;
  if (oldest === undefined) return;
  const enc = encoderCache.get(oldest);
  if (enc) enc.free();
  encoderCache.delete(oldest);
}

function evictOldestStaticTokenIfNeeded(): void {
  if (staticTokenCache.size <= MAX_STATIC_TOKEN_CACHE) return;
  const oldest = staticTokenCache.keys().next().value;
  if (oldest !== undefined) staticTokenCache.delete(oldest);
}

function getEncoder(model: string): Encoder {
  const cached = encoderCache.get(model);
  if (cached) {
    touchMapEntry(encoderCache, model, cached);
    return cached;
  }

  const enc = encoding_for_model(model as never);
  encoderCache.set(model, enc);
  evictOldestEncoderIfNeeded();
  return enc;
}

function getStaticTokens(
  model: string,
  systemPrefix: string,
  enc: Encoder,
): number {
  const key = `${model}\x1f${systemPrefix}`;
  const cached = staticTokenCache.get(key);
  if (cached !== undefined) {
    touchMapEntry(staticTokenCache, key, cached);
    return cached;
  }

  const value = countTokens(enc, systemPrefix);
  staticTokenCache.set(key, value);
  evictOldestStaticTokenIfNeeded();
  return value;
}

export function clearPromptBudgetCaches(): void {
  for (const enc of encoderCache.values()) enc.free();
  encoderCache.clear();
  staticTokenCache.clear();
}

function truncateToTokenBudget(
  enc: Encoder,
  text: string,
  maxTokens: number,
): string {
  if (maxTokens <= 0) return "";

  const tokens = enc.encode(text);
  if (tokens.length <= maxTokens) return text;
  const clipped = tokens.slice(0, maxTokens);
  return decoder.decode(enc.decode(clipped));
}

function buildPrompt(
  systemPrefix: string,
  history: string[],
  query: string,
): string {
  const rows: string[] = [];
  rows.push(systemPrefix.trim());
  rows.push("");
  rows.push("Conversation context:");

  for (let i = 0; i < history.length; i++) {
    rows.push(`- Turn ${i + 1}: ${history[i]}`);
  }

  rows.push("");
  rows.push(`User request: ${query}`);
  return rows.join("\n");
}

export function preparePromptHost(input: PromptInput): PromptPlan {
  const model = input.model;
  const maxInputTokens = Math.max(64, input.maxInputTokens);
  const cleanHistory = input.history.map(normalizeText).filter(Boolean);
  let history = [...cleanHistory];
  let query = normalizeText(input.query);
  const enc = getEncoder(model);

  const staticTokens = getStaticTokens(model, input.systemPrefix, enc);

  let prompt = buildPrompt(input.systemPrefix, history, query);
  const rawInputTokens = countTokens(enc, prompt);
  let inputTokens = rawInputTokens;
  let trimmedTurns = 0;
  let queryWasTrimmed = false;

  while (inputTokens > maxInputTokens && history.length > 0) {
    history.shift();
    trimmedTurns++;
    prompt = buildPrompt(input.systemPrefix, history, query);
    inputTokens = countTokens(enc, prompt);
  }

  if (inputTokens > maxInputTokens) {
    const promptWithoutQuery = buildPrompt(input.systemPrefix, history, "");
    const promptWithoutQueryTokens = countTokens(enc, promptWithoutQuery);
    const remainingBudget = Math.max(
      16,
      maxInputTokens - promptWithoutQueryTokens,
    );
    const clipped = truncateToTokenBudget(enc, query, remainingBudget);
    queryWasTrimmed = clipped.length < query.length;
    query = clipped;
    prompt = buildPrompt(input.systemPrefix, history, query);
    inputTokens = countTokens(enc, prompt);
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

export const preparePrompt = task<PromptInput, PromptPlan>({
  f: (input) => preparePromptHost(input),
});

export function preparePromptFastHost(input: PromptInput): PromptPlanFast {
  const plan = preparePromptHost(input);
  return {
    rawInputTokens: plan.rawInputTokens,
    inputTokens: plan.inputTokens,
    staticTokens: plan.staticTokens,
    dynamicTokens: plan.dynamicTokens,
    trimmedTurns: plan.trimmedTurns,
    queryWasTrimmed: plan.queryWasTrimmed,
  };
}

export function preparePromptBatchFastHost(
  inputs: PromptInput[],
): PromptBudgetSummary {
  let totals: PromptBudgetSummary = {
    rawTokens: 0,
    budgetedTokens: 0,
    staticTokens: 0,
    dynamicTokens: 0,
    trimmedRuns: 0,
    queryTrimmedRuns: 0,
    turnsDropped: 0,
  };

  for (let i = 0; i < inputs.length; i++) {
    const plan = preparePromptFastHost(inputs[i]!);
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

export const preparePromptBatchFast = task<PromptInput[], PromptBudgetSummary>({
  f: (inputs) => preparePromptBatchFastHost(inputs),
});
