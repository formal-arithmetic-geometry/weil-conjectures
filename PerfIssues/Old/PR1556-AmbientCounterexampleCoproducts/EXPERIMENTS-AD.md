# DefEq Internal Cost Experiments

Case: `PR1556-AmbientCounterexampleCoproducts`
Lean / Mathlib: Lean 4.35.0, snapshot `1ef1fddac73`

## A1: decomposition

Root: the generated congruence proposition domain containing the
`CategoryStruct.comp`/`NatTrans.app` major premise. The selected counters root
was 6,670,198 calls, depth 213, 77.188 s wall, split into 39.404 s exclusive
comparison and 37.784 s reduction. The trace root was 95.643 s with the same
call count. It recorded 276,829 Pi-domain comparisons, 126,864 proposition
comparisons, and 3,352,429 proof attempts. WHNF took 42.864 s in the trace;
Delta took 1.491 s across 13,242,067 unfolds. Thus reduction is substantial,
but the recursive comparison share is also large.

The bounded pair sample contained 3,428,653 distinct exact pairs and 1,571,347
repeats; repeats contributed 565 ms (about 1.1%) of trace comparison-exclusive
time. Top exclusive children were `SMul.smul` (528 ms), `HAdd.hAdd` (502 ms),
`Eq` (251 ms), and `AddCommGroup.proj` (228 ms). Proposition timers are nested
and cannot be added to the root categories. No allocation/GC counters were
available.

## READY2 rerun

The selected trace root is `root=826`. Its largest path prefixes are the
`CategoryStruct.comp`/`comp` chain under `argument[7]` and its nested
`NatTrans.app` nodes, with the first major subtree at 76,274.013 ms. The trace
root measured 92,750.164 ms wall, with 48,035.017 ms comparison exclusive and
44,715.147 ms reduction exclusive. Counters measured 61,051.306 ms,
29,147.176/31,904.129 ms. Dependent comparison/reduction timers were
38,426.569/35,445.108 ms (80.0% of comparison-exclusive); proposition
comparison/reduction were 9,557.184/9,207.893 ms and are nested.

READY2 created 298,357,470 C++ expressions (9,970,769,744 bytes). RSS/commit
delta was 103,219,200 bytes in trace (106,168,320 in counters). `/usr/bin/time`
reported 4:58.47 wall and 8,662,560 KB maximum RSS for the trace run.

## A2: targeted ablation

The A1 target is the `NatTrans.app` major premise. Replacing only the right
major premise with the left term, while retaining the congruence consumer and
dependent proposition, checked in 0 ms. The original A/B conversion was
50,090 ms and the reverse B/A restoration was 50,585 ms. The exact result type
was unchanged and the replacement Kernel-checked, so this is a valid causal
ablation of that component. The remaining parent work is not attributable to a
single child from the trace: it is a deep mixed tree with many small children.

## B and C status

No valid B three-way provider exists in this generated congruence: adding a
shared local provider changes the generated proposition. No independent
field-count control preserves the same theorem obligation. Both are recorded
as invalid attempts. The old/fixed closing proof is an API control, not a
provider-sharing measurement.

## Accounting and artifacts

`probes/ad/profile.txt` points to the replay/source trace and the A/A and B/A
baseline probes. The source prefix was 60.57 s wall / 7,760,464 KB RSS; the
fixed prefix was 5.73 s / 3,056,716 KB. Instrumentation overhead is reported
from the validated common controls in the NativePullTensor record.
