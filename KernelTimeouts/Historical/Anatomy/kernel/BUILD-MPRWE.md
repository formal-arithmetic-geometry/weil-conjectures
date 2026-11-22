# READY3 MPRWE observational kernel build

READY3 extends the READY2 type checker instrumentation for Lean 4.33.1
(`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`) and Lean 4.35.0
(`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`). The changes are observational:
conversion order, transparency, caches, and shortcuts are unchanged.

The patch adds bounded JSONL events selected by `LEAN_DEFEQ_MPRWE_EVENTS`:
enter/exit records carry root, call, parent, depth, heads, argument/field
path category, orthogonal tags, a structural context fingerprint, result,
and exclusive/reduction time. Reduction records carry before and after heads
and the phase that exposed them. Counters mode emits the aggregate report;
trace mode additionally emits the bounded raw events. Provenance is assigned
by the offline analyzer after manual review; ambiguous nodes remain
`Unclassified`.

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
`LEAN_DEFEQ_MPRWE_MAX_EVENTS` and are kept below 20 MB.

Process wall includes imports and elaboration. The base 4.33.1 run was
slower than its READY2 historical source run, so overhead is reported as a
measured paired run and not as a normalized claim. Counter-mode root shares
remain the quantitative timings; trace mode is for tree shape and event
reconstruction.

## Offline analysis

Run `python3 mprwe_analyze.py <events.jsonl>`. The default root is the most
frequent captured root; use `--root N` to select a process-local root serial.
The analyzer reports calls and exclusive time for M0, M1, M2, Matched, and
Unclassified. It uses conservative structural rules and cannot establish
semantic mismatch provenance without expression and context review.
