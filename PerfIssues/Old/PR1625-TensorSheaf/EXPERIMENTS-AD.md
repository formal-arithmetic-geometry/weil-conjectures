# DefEq Internal Cost Experiments

Case: `PR1625-TensorSheaf`
Lean / Mathlib: Lean 4.35.0, snapshot `1ef1fddac73`

## A1: decomposition

Root: the final inferred/declared conversion for
`leftDerivedUpperStarTensorComparison_app_app_fac`, with nested
`NatTrans.app` applications. The selected counters root was 11,757,788 calls,
depth 125, 127.840 s wall, with 70.713 s exclusive comparison and 57.127 s
exclusive reduction. The trace reproduced the root and reached 142.050 s.
It made 34,035,091 WHNF requests (59.679 s), 19,411,491 Delta unfolds
(2.183 s), 84,756 Pi-domain comparisons, 155,955 proposition comparisons,
and 5,235,311 proof attempts.

The bounded trace sample had 3,284,552 distinct exact pairs and 1,715,448
repeats; repeats contributed 377 ms (0.5%) of comparison-exclusive time.
Top exclusive children included `CategoryStruct.comp` (1.003 s), `NatTrans.app`
(542 ms), `NSMul.proj` (473 ms), `AddGroup.proj` (472 ms), and `Functor.obj`
(242 ms). No single child accounts for the parent; the outer and inner app
sites have the same measured shape (about 95.7--97.2 s at release speed).

## READY2 rerun

The selected trace root is `root=7086`. The largest path prefixes are the
outer `CategoryStruct.comp`/`NatTrans.app` chain under `binder_body[15]`,
followed by the inner composition and app chain; the outer subtree measured
141,308.590 ms. The trace root measured 142,415.392 ms wall, with
82,161.913 ms comparison exclusive and 60,253.479 ms reduction exclusive.
Counters measured 97,208.037 ms, split 49,660.504/47,547.533 ms. Dependent
comparison/reduction timers were 62,604.213/49,357.493 ms (76.2% of
comparison-exclusive); proposition comparison/reduction were 19,556.990/
10,895.986 ms and are nested.

READY2 created 438,450,718 C++ expressions (14,677,924,016 bytes). RSS/commit
delta was 5,442,961,408 bytes in trace (65,404,928 in counters). `/usr/bin/time`
reported 7:04.87 wall and 9,578,116 KB maximum RSS for the trace run.

## A2: targeted ablation

The selected component is the outer `NatTrans.app` major premise. Original A/B
was 95,869 ms, A/A replacement was 0 ms, and B/A restoration was 93,567 ms.
The outer `CategoryStruct.comp`, both app layers, and dependent result type
were retained, and the replacement type-checked. This is a valid causal
ablation. The isolated inner app and enclosing composition remained expensive
(95,717 and 96,236 ms), showing that nesting preserves the same internal
component rather than adding a cheap wrapper-only cost.

## B and C status

No valid independently reconstructed provider or field-count matrix preserves
the nested dependent `NatTrans.app` obligation. Synthetic depth variants were
rejected as a different telescope, so B/C are invalid rather than claimed.

## Accounting and artifacts

`probes/ad/profile.txt` records the root trace and the original/A/A/B/A
replays. The original target conversion was 97,215 ms; the aligned theorem
control was 2.43 s. Proposition timing is inclusive and is not added to the
exclusive comparison/reduction split. Allocation/GC attribution is unavailable.
