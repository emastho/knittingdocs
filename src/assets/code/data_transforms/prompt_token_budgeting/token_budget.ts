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

const decoder = new TextDecoder();

function normalizeText(value: string): string {
  return value.replace(/\s+/g, " ").trim();
}

function countTokens(model: string, text: string): number {
  const enc = encoding_for_model(model as never);
  try {
    return enc.encode(text).length;
  } finally {
    enc.free();
  }
}

function truncateToTokenBudget(
  model: string,
  text: string,
  maxTokens: number,
): string {
  if (maxTokens <= 0) return "";

  const enc = encoding_for_model(model as never);
  try {
    const tokens = enc.encode(text);
    if (tokens.length <= maxTokens) return text;
    const clipped = tokens.slice(0, maxTokens);
    return decoder.decode(enc.decode(clipped));
  } finally {
    enc.free();
  }
}

function buildPrompt(systemPrefix: string, history: string[], query: string): string {
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

  const staticTokens = countTokens(model, input.systemPrefix);

  let prompt = buildPrompt(input.systemPrefix, history, query);
  const rawInputTokens = countTokens(model, prompt);
  let inputTokens = rawInputTokens;
  let trimmedTurns = 0;
  let queryWasTrimmed = false;

  while (inputTokens > maxInputTokens && history.length > 0) {
    history.shift();
    trimmedTurns++;
    prompt = buildPrompt(input.systemPrefix, history, query);
    inputTokens = countTokens(model, prompt);
  }

  if (inputTokens > maxInputTokens) {
    const promptWithoutQuery = buildPrompt(input.systemPrefix, history, "");
    const promptWithoutQueryTokens = countTokens(model, promptWithoutQuery);
    const remainingBudget = Math.max(16, maxInputTokens - promptWithoutQueryTokens);
    const clipped = truncateToTokenBudget(model, query, remainingBudget);
    queryWasTrimmed = clipped.length < query.length;
    query = clipped;
    prompt = buildPrompt(input.systemPrefix, history, query);
    inputTokens = countTokens(model, prompt);
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
