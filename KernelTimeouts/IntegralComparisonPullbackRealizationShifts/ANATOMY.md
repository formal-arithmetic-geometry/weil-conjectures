# DEF EQ COST ANATOMY REPORT

Case: IntegralComparisonPullbackRealizationShifts. Lean 4.35.0 (`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`); Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`; source snapshot: `b400b43ec29; integralComparisonPullbackRealization_commShift`. Kernel source checksum: `8982321f70352a7c775c77e66e2f25dbf71ea9de7fe978fffb8f600862b7d566` (instrumented `type_checker.cpp` used by the READY build). Root conversion ID: `IC-change-v1`.

## 1. Root

The explicit `change` goal conversion after `commShift_of_localization` and `intro P m`. Both goals are equations of category-morphism compositions; the first raw type difference under `Quiver.Hom`/`Functor.obj`/`DerivedCategory` is `integralTowerHasDerivedCategory` versus `integralOperationsCommHasDerivedCategory`. The suffix `sorry` is after the checked `change`.

Immutable probe: `probes/anatomy/aligned-prefix-after-change.lean`. The raw left/right expressions and local context are recorded in `probes/HeadAudit.lean`. Release diagnostic run: 1:28.56 wall, 88.96 s user CPU, 8374520 KB peak RSS. Separate plain run: 1:24.45 wall and 8368220 KB RSS. Counters-only: 110.020 s root wall; 68.656 s comparison-exclusive (62.4%); 41.363 s WHNF-exclusive (37.6%). Whole-file counters run: 2:23.09 wall. Detailed trace root: 126.587 s; whole-file trace run: 2:43.41 wall, 12066916 KB RSS. The root result is success.

## 2. Reduction cost

WHNF requests 28,206,595; exclusive WHNF time 41.363 s. Delta events 15,114,530, nested Delta timer 1.853 s; Beta 14,444,602, Iota 20,325, Zeta 289,508, projection 1,815,424. Per-operation Beta/Iota/Zeta/projection exclusive times are not exposed. Top Delta heads by direct timed span in the trace (each span can overlap the comparison/WHNF partition):

| Constant | Unfolds | Delta ms |
|---|---:|---:|
| `HAdd.hAdd` | 1,193,784 | 199.830 |
| `PresheafOfModules.obj` | 1,047,896 | 164.168 |
| `AddMonoid.toAdd` | 812,273 | 113.262 |
| `CategoryTheory.Functor.obj` | 332,976 | 94.460 |
| `SubNegMonoid.toAddMonoid` | 632,337 | 80.732 |
| `DFunLike.coe` | 463,152 | 72.952 |
| `instHAdd` | 588,154 | 71.370 |
| `AddCommMagma.toAdd` | 375,504 | 62.455 |

## 3. Recursive comparison cost

Total 9,426,253 calls: 9,353,653 successful, 72,600 failed/stuck/exception; max depth 183. Comparison-exclusive time 68.656 s. Branch counts: quick 4,788,627, quick_reduced 108,685, proof_irrelevance 167,994, lazy_delta 63,701, projection 2,096,326, second_whnf 481,421, application 1,664,481, failure 55,018.

Depth histogram: 66 buckets in the trace; `depth>=64` is grouped by 64-level buckets. Fan-out histogram: 16 buckets, 4,795,430 leaves, 2,644,345 single-child calls, 1,986,478 multi-child calls; maximum recorded bucket 21. Full depth, fan-out and kind-pair histograms are in `probes/anatomy/logs/aligned-prefix-after-change.trace.stderr`. The Kernel patch records child heads and child counts, but not argument/field paths or descendant counts per top child.

Top 20 children by **trace-mode** exclusive time (parent ID, depth, heads, children, exclusive/inclusive/reduction time are preserved verbatim):

```text
ANATOMY child=8270772 parent=8270771 depth=116 children=1 left=Add.proj right=Add.proj exclusive_ms=1087.664 inclusive_ms=1087.860 reduction_ms=0.011
ANATOMY child=4550950 parent=4550949 depth=106 children=4 left=AddSemigroup.mk right=AddSemigroup.mk exclusive_ms=502.009 inclusive_ms=502.424 reduction_ms=0.003
ANATOMY child=4071126 parent=4071125 depth=98 children=1 left=Add.proj right=Add.proj exclusive_ms=494.037 inclusive_ms=494.053 reduction_ms=0.008
ANATOMY child=2250265 parent=2250264 depth=106 children=3 left=Add.add right=Add.add exclusive_ms=255.956 inclusive_ms=256.157 reduction_ms=0.015
ANATOMY child=4641032 parent=4641026 depth=90 children=21 left=LinearMap.comp right=LinearMap.comp exclusive_ms=252.280 inclusive_ms=255.810 reduction_ms=0.003
ANATOMY child=2012276 parent=2012275 depth=103 children=1 left=AddGroup.proj right=AddGroup.proj exclusive_ms=233.396 inclusive_ms=233.505 reduction_ms=0.016
ANATOMY child=2306727 parent=2306724 depth=96 children=2 left=DFunLike.coe right=DFunLike.coe exclusive_ms=123.434 inclusive_ms=123.812 reduction_ms=0.012
ANATOMY child=1117584 parent=1117583 depth=131 children=1 left=MulAction.proj right=MulAction.proj exclusive_ms=106.096 inclusive_ms=106.345 reduction_ms=0.001
ANATOMY child=998409 parent=998408 depth=102 children=3 left=Sub.sub right=Sub.sub exclusive_ms=104.935 inclusive_ms=105.237 reduction_ms=0.024
ANATOMY child=1156980 parent=1156620 depth=92 children=4 left=AddCommGroup.toAddCommMonoid right=AddCommGroup.toAddCommMonoid exclusive_ms=53.018 inclusive_ms=53.342 reduction_ms=0.006
ANATOMY child=494524 parent=494518 depth=121 children=2 left=DFunLike.coe right=DFunLike.coe exclusive_ms=51.534 inclusive_ms=51.557 reduction_ms=0.022
ANATOMY child=552525 parent=552524 depth=111 children=1 left=MulAction.proj right=MulAction.proj exclusive_ms=51.162 inclusive_ms=51.402 reduction_ms=0.002
ANATOMY child=560286 parent=560285 depth=117 children=2 left=6 right=6 exclusive_ms=28.571 inclusive_ms=30.190 reduction_ms=0.000
ANATOMY child=276930 parent=276929 depth=94 children=1 left=Add.proj right=Add.proj exclusive_ms=26.857 inclusive_ms=26.946 reduction_ms=0.001
ANATOMY child=248074 parent=248064 depth=87 children=1 left=AddCommGroup.add_comm right=AddCommGroup.add_comm exclusive_ms=26.644 inclusive_ms=26.999 reduction_ms=0.001
ANATOMY child=141649 parent=141648 depth=86 children=3 left=Add.add right=Add.add exclusive_ms=13.150 inclusive_ms=13.549 reduction_ms=0.038
ANATOMY child=280565 parent=280552 depth=64 children=1 left=AddCommGroup.add_comm right=AddCommGroup.add_comm exclusive_ms=13.143 inclusive_ms=13.378 reduction_ms=0.002
ANATOMY child=126993 parent=126992 depth=89 children=1 left=SubNegMonoid.proj right=SubNegMonoid.proj exclusive_ms=12.026 inclusive_ms=12.075 reduction_ms=0.003
ANATOMY child=143057 parent=143056 depth=71 children=6 left=ModuleCat.Hom._mkInternal right=ModuleCat.Hom._mkInternal exclusive_ms=6.471 inclusive_ms=14.530 reduction_ms=0.001
ANATOMY child=63664 parent=63663 depth=91 children=1 left=SubNegMonoid.proj right=SubNegMonoid.proj exclusive_ms=5.964 inclusive_ms=6.002 reduction_ms=0.005
```

## 4. Dependent and proof-type cost

Pi-domain comparison events 354,892; proof-irrelevance branch entries 167,994; proposition comparisons 167,994. The patch's proposition timer is 398.907 s, but it is inclusive/overlapping (and can exceed root wall), so it cannot be a cost-profile share or a measure of time before proof irrelevance. Instantiated binder, data-field, and proof-type exclusive times are not separately reported.

## 5. Repeated work

Trace captured 5,000,000 ordered expression-node pairs: 3,218,568 distinct exact pairs, 1,781,432 repeated exact entries, and 2,435,441 raw-hash structural groups. Repeated sampled calls accumulated 0.712 s exclusive time in trace mode. Capture is capped at 5,000,000 calls; numbers are sample-only if total calls exceed this. Context identity, reversed-pair tracking, top repeated groups, and actual cache-hit/miss behavior are unavailable. Zero cache counters in this patch do not prove absence of Kernel caching.

## 6. Memory

Release diagnostic peak RSS: 8374520 KB; instrumented trace whole-file peak RSS: 12066916 KB. Expr allocation counts/bytes, live bytes, DAG sharing, GC counts/time, and phase-specific memory attribution are unavailable. RSS is a process proxy, not an allocation cost share.

## 7. Cost profile

F (mixed), comparison-leading (62.4% comparison, 37.6% WHNF); deep to 183 with many multi-child calls. The first raw instance path is not shown to be the dominant timed child.

Only comparison-exclusive and outer WHNF-exclusive timers form the reported root partition. Delta timing, proposition timing, and repeated-pair timing are nested or overlapping and must not be added. The patch charges bookkeeping overhead to calls; trace-mode top-child spikes can include pair-map growth and are qualitative. No separate instrumentation-overhead or other-Kernel category is measured at this root. Direct Delta time lacks left/right attribution.

## 8. Control comparison

The prefix before `change` checks in 6.20 s versus 88.56 s with `change` and diagnostics. This localizes whole-file cost to the added conversion but is not an aligned same-root control. The copied instance-alignment attempt cannot run here: its `HeadAuditTools` meta import lacks a built `.olean` in the current library tree. No control-call delta is claimed.

## 9. Conclusion

`PresheafOfModules.obj` has 1.05 million Delta steps but only about 0.16 s measured direct Delta time in the trace. The root cost is the broad recursive comparison/reduction workload, not proven intrinsic expense of that definition. The exact dominant semantic pair remains unresolved.

Measured claims are the release diagnostic, counters-only, and trace numbers above. Inferences about the semantic path rely on the preserved raw expression audit. Trace top-20 paths, per-child repeat counts, exact allocation costs, and a non-overlapping dependent/proof-type split are limitations of the supplied instrumentation.
