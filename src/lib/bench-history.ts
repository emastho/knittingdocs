// The historical Markdown reports and JSON exports contain different runs.
// Use the reports behind the published charts, and fail the build if a row is missing.
import { readFileSync } from 'node:fs';
import { RUNTIMES, RUNTIME_NAMES, type RuntimeId } from './bench';
import tokioReport from '../assets/tokio/summary.md?raw';

const reports = import.meta.glob<string>('../assets/results/*.md', {
  eager: true, query: '?raw', import: 'default',
});
export const runtimeReport = (runtime: RuntimeId, suite: string): string => {
  const path = `../assets/results/${runtime}_${suite}.md`;
  const report = reports[path];
  if (!report) throw new Error(`Missing benchmark report: ${path}`);
  return report;
};
const cells = (line: string) => line.split('|').map((cell) => cell.replace(/[`*]/g, '').trim());
const row = (report: string, label: string) => {
  const line = report.split('\n').find((line) => cells(line)[1] === label);
  if (!line) throw new Error(`Missing benchmark row: ${label}`);
  return cells(line);
};
const timeNs = (value: string) => {
  const match = value.match(/^([\d.]+)\s*(ns|µs|us|ms)/);
  if (!match) throw new Error(`Invalid benchmark time: ${value}`);
  return Number(match[1]) * ({ ns: 1, 'µs': 1e3, us: 1e3, ms: 1e6 }[match[2]]!);
};
const fixed = (value: number) => value.toFixed(1);
const latency = (runtime: RuntimeId, arm: 'knitting' | 'worker', count: number) => {
  const section = runtimeReport(runtime, 'latency').split(`| • ${arm}`)[1];
  if (!section) throw new Error(`Missing ${arm} latency section`);
  return timeNs(row(section, `1 thread → (${count})`)[2]);
};
export const latencyGroups = RUNTIMES.map((runtime) => ({
  label: RUNTIME_NAMES[runtime],
  bars: [
    { label: 'postMessage', value: latency(runtime, 'worker', 1) / 1e3 },
    { label: 'Knitting', value: latency(runtime, 'knitting', 1) / 1e3, knitting: true },
  ],
}));
export const latencyRatios = (count: number) => new Intl.ListFormat("en", { style: "long", type: "conjunction" }).format(RUNTIMES.map((runtime) =>
  `${fixed(latency(runtime, 'worker', count) / latency(runtime, 'knitting', count))}× faster on ${RUNTIME_NAMES[runtime]}`,
));
const primeTime = (runtime: RuntimeId, workers: number) => timeNs(row(
  runtimeReport(runtime, 'withload'), workers === 0 ? 'main' : `main + ${workers} extra threads → full range`,
)[2]) / 1e6;
export const primeSpeedups = Object.fromEntries(RUNTIMES.map((runtime) => [
  runtime, fixed(primeTime(runtime, 0) / primeTime(runtime, 4)),
])) as Record<RuntimeId, string>;
export const primeGroups = [{ bars: [0, 1, 2, 3, 4].map((workers) => {
  const value = primeTime('node', workers);
  return {
    label: workers === 0 ? 'Main thread only' : `${workers} extra thread${workers === 1 ? '' : 's'}`,
    value,
    text: `${Math.round(value)} ms${workers ? ` · ${fixed(primeTime('node', 0) / value)}×` : ''}`,
    knitting: workers > 0,
  };
}) }];
const sweep = tokioReport.split('## Uint8Array Size Sweep Avg Latency')[1]?.split('## Arc Comparison')[0];
if (!sweep) throw new Error('Missing Tokio size sweep');
const copyTime = (size: string, arm: 'tokio' | RuntimeId) => {
  const line = sweep.split('\n').find((line) => cells(line)[0] === size);
  if (!line) throw new Error(`Missing Tokio size: ${size}`);
  return timeNs(cells(line)[{ tokio: 1, bun: 2, node: 3, deno: 4 }[arm]]) / 1e6;
};
export const copyGroups = [{ bars: (['tokio', 'bun', 'node', 'deno'] as const).map((arm) => ({
  label: arm === 'tokio' ? 'Tokio' : `Knitting on ${RUNTIME_NAMES[arm]}`,
  value: copyTime('256 KiB', arm), knitting: arm !== 'tokio',
})) }];
const sizes = ['32 KiB', '64 KiB', '128 KiB', '256 KiB', '512 KiB'];
const savings = (arm: RuntimeId) => sizes.map((size) => 100 * (1 - copyTime(size, arm) / copyTime(size, 'tokio')));
const savingsNodeBun = [...savings('node'), ...savings('bun')];
export const copyRange = {
  fastest: Math.round(Math.min(...savingsNodeBun)), slowest: Math.round(Math.max(...savingsNodeBun)),
  denoLess: Math.round(Math.max(...savings('deno'))), denoMore: Math.round(-Math.min(...savings('deno'))),
};
export const smallCopyLead = fixed(Math.max(...['1 KiB', '2 KiB', '4 KiB', '8 KiB', '16 KiB']
  .flatMap((size) => RUNTIMES.map((runtime) => copyTime(size, runtime) / copyTime(size, 'tokio')))));
const largeRatios = RUNTIMES.map((runtime) => copyTime('1 MiB', runtime) / copyTime('1 MiB', 'tokio'));
export const largeCopyLead = `${fixed(Math.min(...largeRatios))}–${fixed(Math.max(...largeRatios))}×`;

const honoReport = readFileSync(new URL('../../public/documents/hono-16core-benchmark.md', import.meta.url), 'utf8');
const matched = honoReport.split('## B. Open loop, fixed rate - latency')[1]?.split('## C.')[0];
if (!matched) throw new Error('Missing Hono fixed-rate report');
const honoRoutes = ['/ping', '/ssr', '/jwt'].map((route) => {
  const section = matched.split(`**${route}**`)[1];
  if (!section) throw new Error(`Missing Hono route: ${route}`);
  const baseline = row(section, 'hono_only');
  const worker = row(section, 'threads: 1');
  return { route, baseline: Number(baseline[3]), worker: Number(worker[3]), cores: [Number(baseline[4]), Number(worker[4])] };
});
const saturationSection = honoReport.split('## A. Saturating load - throughput')[1]?.split('## B.')[0];
if (!saturationSection) throw new Error('Missing Hono saturation report');
export const hono = {
  reductions: honoRoutes.map(({ baseline, worker }) => Math.round(100 * (1 - worker / baseline))),
  latencyGroups: honoRoutes.map(({ route, baseline, worker }) => ({
    label: `<code>${route}</code>`, bars: [
      { label: 'Hono only', value: baseline }, { label: 'One worker', value: worker, knitting: true },
    ],
  })),
  cpuGroups: [{ bars: honoRoutes[0].cores.map((value, index) => ({
    label: index ? 'One worker' : 'Hono only', value, text: `${value.toFixed(2)} cores`, knitting: index === 1,
  })) }],
  saturation: ['hono_only', 'threads: 1'].map((label) => {
    const values = row(saturationSection, label);
    return { rps: Number(values[5]), cores: Number(values[8]) };
  }),
};

const payloadComparisons = RUNTIMES.flatMap((runtime) => [1, 100].flatMap((count) => {
  const report = runtimeReport(runtime, 'types');
  const knitting = report.split(`| • knitting ${count}`)[1]?.split('| •')[0];
  const worker = report.split(`| • worker ${count}`)[1]?.split('| •')[0];
  if (!knitting || !worker) throw new Error(`Missing ${runtime} payload comparison at ${count}`);
  return knitting.split('\n').filter((line) => /-> \(/.test(cells(line)[1] ?? '')).map((line) => {
    const values = cells(line);
    return {
      runtime, count, label: values[1].split(' -> ')[0],
      ratio: timeNs(row(worker, values[1])[2]) / timeNs(values[2]),
    };
  });
}));
export const payloadComparison = {
  count: new Set(payloadComparisons.map(({ label }) => label)).size,
  allAhead: payloadComparisons.every(({ ratio }) => ratio > 1),
  narrowest: payloadComparisons.reduce((lowest, result) => result.ratio < lowest.ratio ? result : lowest),
};
export const payloadNarrowest = `${fixed(payloadComparison.narrowest.ratio)}×`;
export const payloadGrowth = RUNTIMES.map((runtime) => {
  const report = runtimeReport(runtime, 'call-growth-batch');
  const rate = (arm: string) => {
    const section = report.split(`| • call growth batch ${arm}`)[1]?.split('| •')[0];
    if (!section) throw new Error(`Missing ${runtime} ${arm} growth report`);
    const elapsed = timeNs(row(section, '1048576 B')[2]);
    return (64 * 1048576 / elapsed).toFixed(2);
  };
  return { runtime: RUNTIME_NAMES[runtime], string: rate('string'), binary: rate('uint8array') };
});
export const ipcRatioRange = (arm: 'websocket' | 'http') => {
  const ratios = RUNTIMES.flatMap((runtime) => [1, 25, 50].map((count) => {
    const report = runtimeReport(runtime, 'ipc');
    const knitting = report.split('| • knitting')[1]?.split('| •')[0];
    const comparison = report.split(`| • ${arm}`)[1]?.split('| •')[0];
    if (!knitting || !comparison) throw new Error(`Missing ${runtime} IPC ${arm}`);
    return timeNs(row(comparison, `local → (${count})`)[2]) / timeNs(row(knitting, `1 thread → (${count})`)[2]);
  }));
  return `${fixed(Math.min(...ratios))}–${fixed(Math.max(...ratios))}×`;
};
const idleValues = row(honoReport, 'threads: 15 idle cores');
export const idleCores = { before: Number(idleValues[2]), after: Number(idleValues[3]) };
const repeatLine = honoReport.split('\n').find((line) => line.startsWith('{') && JSON.parse(line).tag === 't1s50');
if (!repeatLine) throw new Error('Missing Hono one-worker repeat');
export const repeatCores: number = JSON.parse(repeatLine).cores;
