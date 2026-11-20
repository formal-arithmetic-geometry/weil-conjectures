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

## READY2 rerun

The selected trace root is `root=2754`. Its leading path prefixes are the
nested `CategoryStruct.comp`/`DFunLike.coe` chain (25,812.968 ms), followed by
the `comp`/`NatTrans.app` subtree (15,663.341 ms) and the `Functor.map` branch
(6,852.367 ms). The trace root measured 28,698.842 ms wall, with
15,785.269 ms comparison exclusive and 12,913.573 ms reduction exclusive.
Counters measured 22,419.324 ms, split 10,744.132/11,675.192 ms. Dependent
comparison/reduction timers were 12,565.977/10,210.169 ms (79.6% of
comparison-exclusive); proposition comparison/reduction were 3,208.523/
2,698.456 ms and are nested.

READY2 created 112,996,826 C++ expressions (3,776,404,760 bytes). RSS/commit
delta was zero in trace and counters for this run. `/usr/bin/time` reported
7:08.31 wall and 12,306,952 KB maximum RSS for the trace run.

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
