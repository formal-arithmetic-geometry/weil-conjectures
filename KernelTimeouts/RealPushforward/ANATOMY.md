# DEF EQ COST ANATOMY REPORT

Case: RealPushforward. Lean 4.35.0 (`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`); Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`; source snapshot: `ed3d39ddb5d; isReal_higherLowerShriek_one`. Kernel source checksum: `8982321f70352a7c775c77e66e2f25dbf71ea9de7fe978fffb8f600862b7d566` (instrumented `type_checker.cpp` used by the READY build). Root conversion ID: `RP-final-exact-v1`.

## 1. Root

Final `exact this` inferred-type/goal comparison after the polynomial rewrites. Under `Polynomial.coeff`, the inferred polynomial is `LinearMap.charpolyRev ...` and the goal uses `FrobeniusModule.localPolynomial ...`. `probes/HeadAudit.lean` preserves the full pair.

Immutable probe: `probes/anatomy/original-FinalExact.lean`. The raw left/right expressions and local context are recorded in `probes/HeadAudit.lean`. Release diagnostic run: 0:57.44 wall, 56.44 s user CPU, 4759316 KB peak RSS. Separate plain run: 0:56.14 wall and 4755164 KB RSS. Counters-only: 63.942 s root wall; 63.938 s comparison-exclusive (100.0%); 0.004 s WHNF-exclusive (0.0%). Whole-file counters run: 1:13.44 wall. Detailed trace root: 79.129 s; whole-file trace run: 1:29.46 wall, 6247708 KB RSS. The root result is a deterministic Kernel timeout, so these are partial-root numbers.

## 2. Reduction cost

WHNF requests 1,120; exclusive WHNF time 0.004 s. Delta events 33,162,751, nested Delta timer 1.786 s; Beta 10,356,973, Iota 4, Zeta 35,366, projection 1,430,816. Per-operation Beta/Iota/Zeta/projection exclusive times are not exposed. Top Delta heads by direct timed span in the trace (each span can overlap the comparison/WHNF partition):

| Constant | Unfolds | Delta ms |
|---|---:|---:|
| `DFunLike.coe` | 2,861,582 | 492.851 |
| `AlgebraicGeometry.Scheme.Hom.toLRSHom'` | 2,861,481 | 142.373 |
| `Function.comp` | 2,861,471 | 126.703 |
| `TopCat.Hom.hom'` | 2,861,477 | 125.528 |
| `AlgebraicGeometry.LocallyRingedSpace.Hom.toHom` | 2,861,479 | 120.422 |
| `AlgebraicGeometry.Scheme.Hom.toLRSHom` | 2,861,481 | 119.199 |
| `ContinuousMap.toFun` | 2,861,472 | 117.909 |
| `AlgebraicGeometry.PresheafedSpace.Hom.base` | 2,861,477 | 116.455 |

## 3. Recursive comparison cost

Total 17,340,236 calls: 4,977,433 successful, 12,362,803 failed/stuck/exception; max depth 91. Comparison-exclusive time 63.938 s. Branch counts: quick 4,996,435, quick_reduced 9,773, proof_irrelevance 207, lazy_delta 1,430,775, projection 20, second_whnf 47, application 28, failure 10,902,868, exception 83.

Depth histogram: 65 buckets in the trace; `depth>=64` is grouped by 64-level buckets. Fan-out histogram: 18 buckets, 6,477,076 leaves, 10,047,881 single-child calls, 815,279 multi-child calls; maximum recorded bucket 18. Full depth, fan-out and kind-pair histograms are in `probes/anatomy/logs/original-FinalExact.trace.stderr`. The Kernel patch records child heads and child counts, but not argument/field paths or descendant counts per top child.

Top 20 children by **trace-mode** exclusive time (parent ID, depth, heads, children, exclusive/inclusive/reduction time are preserved verbatim):

```text
ANATOMY child=11349068 parent=11349067 depth=82 children=1 left=DFunLike.coe right=DFunLike.coe exclusive_ms=444.728 inclusive_ms=444.873 reduction_ms=0.000
ANATOMY child=4975530 parent=4975515 depth=83 children=1 left=ContinuousMap.proj right=Function.comp exclusive_ms=216.220 inclusive_ms=216.437 reduction_ms=0.000
ANATOMY child=5582422 parent=5582421 depth=82 children=1 left=DFunLike.coe right=DFunLike.coe exclusive_ms=212.786 inclusive_ms=212.921 reduction_ms=0.000
ANATOMY child=2449878 parent=2449854 depth=82 children=1 left=ContinuousMap.proj right=Function.comp exclusive_ms=101.825 inclusive_ms=102.032 reduction_ms=0.000
ANATOMY child=2742860 parent=2742859 depth=83 children=1 left=DFunLike.coe right=DFunLike.coe exclusive_ms=101.330 inclusive_ms=101.463 reduction_ms=0.000
ANATOMY child=1206278 parent=1206277 depth=84 children=1 left=DFunLike.coe right=DFunLike.coe exclusive_ms=48.644 inclusive_ms=48.815 reduction_ms=0.000
ANATOMY child=1344675 parent=1344674 depth=84 children=1 left=DFunLike.coe right=DFunLike.coe exclusive_ms=47.956 inclusive_ms=48.080 reduction_ms=0.000
ANATOMY child=655982 parent=655981 depth=83 children=1 left=DFunLike.coe right=DFunLike.coe exclusive_ms=22.893 inclusive_ms=22.950 reduction_ms=0.000
ANATOMY child=593758 parent=593688 depth=81 children=10 left=TopCat.Hom.proj right=ContinuousMap.comp exclusive_ms=22.659 inclusive_ms=22.874 reduction_ms=0.000
ANATOMY child=16539805 parent=16539804 depth=75 children=9 left=Eq.ndrec right=Eq.ndrec exclusive_ms=12.898 inclusive_ms=25.158 reduction_ms=0.000
ANATOMY child=292166 parent=292151 depth=82 children=1 left=ContinuousMap.proj right=Function.comp exclusive_ms=10.871 inclusive_ms=10.947 reduction_ms=0.000
ANATOMY child=316932 parent=316931 depth=83 children=1 left=DFunLike.coe right=DFunLike.coe exclusive_ms=10.848 inclusive_ms=10.911 reduction_ms=0.000
ANATOMY child=13041027 parent=13041026 depth=74 children=9 left=Eq.ndrec right=Eq.ndrec exclusive_ms=10.763 inclusive_ms=23.411 reduction_ms=0.000
ANATOMY child=7933996 parent=7933995 depth=71 children=9 left=Eq.ndrec right=Eq.ndrec exclusive_ms=6.582 inclusive_ms=19.252 reduction_ms=0.000
ANATOMY child=14949399 parent=14949398 depth=67 children=5 left=CategoryTheory.Limits.WidePullbackShape.wideCospan.match_1 right=CategoryTheory.Limits.WidePullbackShape.wideCospan.match_1 exclusive_ms=5.986 inclusive_ms=17.897 reduction_ms=0.000
ANATOMY child=150039 parent=150038 depth=84 children=1 left=DFunLike.coe right=DFunLike.coe exclusive_ms=5.410 inclusive_ms=5.462 reduction_ms=0.000
ANATOMY child=143477 parent=143473 depth=80 children=10 left=CategoryTheory.CategoryStruct.comp right=CategoryTheory.CategoryStruct.comp exclusive_ms=5.385 inclusive_ms=6.823 reduction_ms=0.000
ANATOMY child=5869579 parent=5869578 depth=74 children=9 left=Eq.ndrec right=Eq.ndrec exclusive_ms=4.893 inclusive_ms=17.405 reduction_ms=0.000
ANATOMY child=6997541 parent=6997540 depth=67 children=5 left=CategoryTheory.Limits.WidePullbackShape.wideCospan.match_1 right=CategoryTheory.Limits.WidePullbackShape.wideCospan.match_1 exclusive_ms=2.861 inclusive_ms=14.969 reduction_ms=0.000
ANATOMY child=3687285 parent=3687260 depth=76 children=4 left=5 right=5 exclusive_ms=2.774 inclusive_ms=16.571 reduction_ms=0.000
```

## 4. Dependent and proof-type cost

Pi-domain comparison events 34; proof-irrelevance branch entries 207; proposition comparisons 208. The patch's proposition timer is 68.446 s, but it is inclusive/overlapping (and can exceed root wall), so it cannot be a cost-profile share or a measure of time before proof irrelevance. Instantiated binder, data-field, and proof-type exclusive times are not separately reported.

## 5. Repeated work

Trace captured 5,000,000 ordered expression-node pairs: 1,454,272 distinct exact pairs, 3,545,728 repeated exact entries, and 451,721 raw-hash structural groups. Repeated sampled calls accumulated 10.160 s exclusive time in trace mode. Capture is capped at 5,000,000 calls; numbers are sample-only if total calls exceed this. Context identity, reversed-pair tracking, top repeated groups, and actual cache-hit/miss behavior are unavailable. Zero cache counters in this patch do not prove absence of Kernel caching.

## 6. Memory

Release diagnostic peak RSS: 4759316 KB; instrumented trace whole-file peak RSS: 6247708 KB. Expr allocation counts/bytes, live bytes, DAG sharing, GC counts/time, and phase-specific memory attribution are unavailable. RSS is a process proxy, not an allocation cost share.

## 7. Cost profile

B (recursive comparison dominated) for the partial root: 63.938 s comparison and 0.004 s WHNF before timeout. It is not the proposed shallow reduction-dominated control: 17.34 million calls, 12.36 million failures and depth 91.

Only comparison-exclusive and outer WHNF-exclusive timers form the reported root partition. Delta timing, proposition timing, and repeated-pair timing are nested or overlapping and must not be added. The patch charges bookkeeping overhead to calls; trace-mode top-child spikes can include pair-map growth and are qualitative. No separate instrumentation-overhead or other-Kernel category is measured at this root. Direct Delta time lacks left/right attribution.

## 8. Control comparison

The polynomial-aligned goal checks in 3.00 s baseline whole-file time; with threshold zero its largest recorded instrumented root is 35.158 ms. The original root instead hits the deterministic Kernel timeout after 17,340,236 calls. A remaining semiring-instance difference in the aligned pair is cheap.

Control probe `probes/anatomy/aligned-AlignedGoal.lean`: release 0:03.00 wall, 3199944 KB RSS; largest threshold-zero instrumented root 35.158 ms and 2,873 calls. This is the largest root in the control file, not a stable cross-file conversion ID.

## 9. Conclusion

One source-level `localPolynomial` unfold is necessary, but it leads into a huge comparison tree involving `ContinuousMap`/`DFunLike.coe` heads. The trace refutes the proposed simple-unfolding workload shape on this current toolchain.

Measured claims are the release diagnostic, counters-only, and trace numbers above. Inferences about the semantic path rely on the preserved raw expression audit. Trace top-20 paths, per-child repeat counts, exact allocation costs, and a non-overlapping dependent/proof-type split are limitations of the supplied instrumentation.
