import type { PromptInput } from "./token_budget.ts";

/**
 * Synthetic chat traffic for the two scripts. Nothing here is part of the
 * budgeting logic -- it just produces conversations long enough that a real
 * budget has to trim them.
 */

export const SYSTEM_PREFIX = [
  "You are a documentation assistant for a multi-threading library.",
  "Prefer concrete, short answers grounded in the provided context.",
  "If the data needed to answer is missing, say so directly.",
  "Never invent API surface that was not shown to you.",
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
  "shared memory buffers",
  "work stealing",
];

const DETAIL = [
  "Walk me through the tradeoffs before recommending anything.",
  "Assume a Node 22 service handling a few thousand requests a minute.",
  "We already tried the naive version and it pinned one core.",
  "Include the failure mode we should watch for in production.",
  "Keep the code sample under twenty lines if you can.",
];

function pick<T>(values: T[], i: number): T {
  return values[i % values.length]!;
}

export function buildPromptInputs(
  count: number,
  maxInputTokens: number,
  model = "gpt-4o-mini",
): PromptInput[] {
  const inputs = new Array<PromptInput>(count);

  for (let i = 0; i < count; i++) {
    const turns = 3 + (i % 12);
    const history = new Array<string>(turns);
    for (let t = 0; t < turns; t++) {
      history[t] = `Turn about ${pick(TOPICS, i + t)}: ${
        pick(DETAIL, i + t * 3)
      } Earlier we settled on ${
        pick(TOPICS, i + t + 5)
      }, so keep that decision in mind.`;
    }

    const parts = [
      `Compare ${pick(TOPICS, i)} with ${pick(TOPICS, i + 4)} for our workload.`,
      pick(DETAIL, i),
      "Give a short recommendation, a migration path, and the one metric that tells us it worked.",
    ];

    // Every 17th user pastes a wall of log output. One of those can blow the
    // budget on its own, which is the only case where trimming reaches the query.
    if (i % 17 === 0) {
      for (let k = 0; k < 40; k++) {
        parts.push(
          `[worker ${k % 8}] task=${pick(TOPICS, i + k)} queued=${
            k * 13
          } claimed=${k * 7} elapsed_ms=${(k * 31) % 97}.${k % 10}`,
        );
      }
    }

    inputs[i] = {
      model,
      systemPrefix: SYSTEM_PREFIX,
      history,
      query: parts.join(" "),
      maxInputTokens,
    };
  }

  return inputs;
}

export function batched<T>(values: T[], size: number): T[][] {
  const batches: T[][] = [];
  for (let i = 0; i < values.length; i += size) {
    batches.push(values.slice(i, i + size));
  }
  return batches;
}
