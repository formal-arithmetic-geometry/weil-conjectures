# READY3 MPRWE observational kernel build

READY3 extends the READY2 type checker instrumentation for Lean 4.33.1
(`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`) and Lean 4.35.0
(`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`). The changes are observational:
conversion order, transparency, caches, and shortcuts are unchanged.

## READY3.2 correction

Round 3 found that `root_serial` was thread-local even though the event stream
was process-wide. Worker threads could therefore reuse a numeric root ID and
mix aggregate rows. READY3.2 uses a process-wide relaxed atomic serial for
both releases; the per-thread call tree and timing state remain unchanged.
`mprwe_analyze.py` now prefers a root with actual raw coverage when selecting
the default root. The old NativePullTensor 120-second validation partition is
invalidated by this identity collision and is not used for shares.

The patch adds bounded JSONL events selected by `LEAN_DEFEQ_MPRWE_EVENTS` and
optionally `LEAN_DEFEQ_MPRWE_ROOT`: enter/exit records carry root, call,
parent, depth, heads, stable whole-expression hashes, the first divergent
path and subterm hashes, the parent's divergent hashes, argument/field path
category, orthogonal tags, context fingerprint, result, and
exclusive/reduction time. Reduction records carry before/after heads and
hashes and the phase that exposed them. A process-wide raw-event cap prevents
large multi-root traces; complete calls are aggregated by provenance and a
bounded path prefix, with an `__other__` bucket when needed. Coverage records
report traced calls and exclusive time against complete root totals.

## Validation

Both patches apply to pristine release worktrees and retain the release
githash. The 4.33.1 and 4.35.0 smoke probes pass. The Tensor slow controls
return the same result and recursive call counts as READY2:

| Release | Base wall | READY3 counters wall | Root calls | Root result |
|---|---:|---:|---:|---|
| 4.33.1 | 63.04 s | 51.33 s | 6,269,774 | true |
| 4.35.0 | 49.63 s | 51.63 s | 2,685,580 | true |

The 4.33.1 Cone timeout has 12,220,823 calls and the same deterministic
timeout as READY2. Its detailed trace has 12,220,823 calls and a 127.540 s
instrumented root. The 4.35.0 Tensor detailed trace has 2,685,580 calls and
a 27.191 s root. Trace event files are capped by
`LEAN_DEFEQ_MPRWE_MAX_EVENTS` (use 4000 for the expanded round-2 schema) and
are kept below 20 MB. The selected-root filter is useful when a process has
many elaboration roots.

Process wall includes imports and elaboration. The base 4.33.1 run was
slower than its READY2 historical source run, so overhead is reported as a
measured paired run and not as a normalized claim. Counter-mode root shares
remain the quantitative timings; trace mode is for tree shape and event
reconstruction.

## Offline analysis

Run `python3 mprwe_analyze.py <events.jsonl>`. The default root is the root
with the largest complete aggregate; use `--root N` to select a process-local
root serial. The analyzer sums aggregate calls and exclusive time, reports
traced-call and traced-time coverage, and prints the top ten captured nodes
for review. Kernel-side labels use structural hashes and parent reduction
history: M1 is a carried divergence, M2 is a divergence first seen after an
exposing reduction, Matched is hash-equal at entry, and only undecidable
records remain Unclassified.
