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
