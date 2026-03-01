#!/usr/bin/env bash
set -euo pipefail

BASE="${BASE:-http://localhost:3000}"
DURATION="${DURATION:-30s}"
C="${C:-50}"              # per-route concurrency (total ~= 3*C)

OUTDIR="${OUTDIR:-oha_mixed_$(date +%Y%m%d_%H%M%S)}"
mkdir -p "$OUTDIR"

SSR_BODY='{"name":"Ari","plan":"pro","bio":"Building on Knitting","projects":17}'
JWT_BODY='{"user":{"id":"u_42","email":"ari@example.com","role":"admin"},"ttlSec":900}'

echo "Target: $BASE"
echo "Duration: $DURATION"
echo "Concurrency per route: $C (total ~= $((C*3)))"
echo "Output dir: $OUTDIR"
echo

# ---------------------------
# Run all 3 in parallel (JSON)
# ---------------------------
oha -z "$DURATION" -c "$C" \
  "$BASE/ping" \
  --no-tui --output-format json -o "$OUTDIR/ping.json" &

oha -z "$DURATION" -c "$C" \
  -m POST -T "application/json" -d "$SSR_BODY" \
  "$BASE/ssr" \
  --no-tui --output-format json -o "$OUTDIR/ssr.json" &

oha -z "$DURATION" -c "$C" \
  -m POST -T "application/json" -d "$JWT_BODY" \
  "$BASE/jwt" \
  --no-tui --output-format json -o "$OUTDIR/jwt.json" &

wait
echo
echo "Runs complete. Computing tail stats…"
echo

# ---------------------------
# Summarize from JSON
# ---------------------------
python3 - <<PY
import json, os, math

outdir = "${OUTDIR}"
files = {
  "ping": os.path.join(outdir, "ping.json"),
  "ssr":  os.path.join(outdir, "ssr.json"),
  "jwt":  os.path.join(outdir, "jwt.json"),
}

def ms(x):
    return None if x is None else float(x) * 1000.0

def fmt(x):
    if x is None or (isinstance(x, float) and math.isnan(x)):
        return "n/a"
    return f"{x:8.2f}"

def show(name, path):
    d = json.load(open(path, "r", encoding="utf-8"))
    s = d.get("summary", {})
    lp = d.get("latencyPercentiles", {})
    sc = d.get("statusCodeDistribution", {}) or {}

    rps = s.get("requestsPerSec", float("nan"))
    total = s.get("total", 0)
    sr = s.get("successRate", 0.0)
    sr_pct = sr * 100.0   # FIXED: successRate is ratio [0,1]

    ok = int(sc.get("200", 0) or 0)
    non_200 = sum(int(v or 0) for k, v in sc.items() if str(k) != "200")

    slow = ms(s.get("slowest"))
    avg  = ms(s.get("average"))
    p50  = ms(lp.get("p50"))
    p99  = ms(lp.get("p99"))
    p999 = ms(lp.get("p99.9"))
    p9999 = ms(lp.get("p99.99"))

    print(f"== {name.upper()} ==")
    print(f"  rps:       {rps:8.2f}")
    print(f"  success:   {sr_pct:6.2f}%")
    print(f"  total:     {total}")
    print(f"  200s:      {ok}")
    print(f"  non-200:   {non_200}")
    print(f"  p50:       {fmt(p50)} ms")
    print(f"  avg:       {fmt(avg)} ms")
    print(f"  p99:       {fmt(p99)} ms")
    print(f"  p99.9:     {fmt(p999)} ms")
    print(f"  p99.99:    {fmt(p9999)} ms")
    print(f"  slowest:   {fmt(slow)} ms")
    print()

for k, p in files.items():
    show(k, p)

print("JSON files:")
for k, p in files.items():
    print(f"  {k}: {p}")
PY

echo "Done."
