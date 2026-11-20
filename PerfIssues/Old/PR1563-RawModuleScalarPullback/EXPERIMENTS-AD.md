# DefEq Internal Cost Experiments

Case: `PR1563-RawModuleScalarPullback`
Lean / Mathlib: Lean 4.35.0, snapshot `1ef1fddac73`

## A1: decomposition

Root: the seven-argument `CategoryStruct.comp` in the dependent `Eq.mpr`
domain. The selected counters root was 2,573,989 calls, depth 95, 33.224 s
wall, split into 16.070 s comparison and 17.154 s reduction. The detailed
trace was 40.875 s; it recorded 8,470,713 WHNF requests (18.647 s), 4,993,230
Delta unfolds (580 ms), 116,765 Pi-domain comparisons, 48,776 proposition
comparisons, and 1,296,043 proof attempts. Pair capture found 1,723,710
distinct exact pairs and 850,279 repeats; repeated entries contributed 409 ms
(1.8%) of comparison-exclusive time. Top children were `HSMul.hSMul`
(1.111 s), `NSMul.proj` (235 ms), `Add.add` (108 ms), and
`SemigroupAction.proj` (52 ms). The seven argument timings were
1/0/2,331/2,274/2,387/6,809/22,374 ms, so the work is distributed, led by
the nested composition and `Functor.map` paths.

## A2: targeted ablation

The measured top component is the nested argument-6 `CategoryStruct.comp`.
One-at-a-time replacements preserved a checked dependent result but left
substantial conversion (independent tested replacements: 18,975--20,810 ms;
outer argument 6: 22,155 ms). No single major-premise abstraction preserved
the exact original composition type with a reversible restored pair, so this
is only partial ablation evidence, not a causal A2 claim. The valid conclusion
is that no tested child explains the complete 31.026 s outer conversion.

## B and C status

The nested composition supplies local amplification and repeated vocabulary,
but a synthetic shared-provider/depth matrix changes dependent morphism types.
No valid B three-way comparison was forced. The seven-argument replacements
are partial C evidence: every retained replacement remains expensive.

## Accounting and artifacts

`probes/ad/profile.txt` records the seven argument measurements and selected
trace. Original and fixed source prefixes were 117.04 s and 50.98 s wall. The
20.699 s aligned root is a broader construction control, not a single-field
ablation. Allocation/GC counters were unavailable.
