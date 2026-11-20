# DEF EQ COST ANATOMY REPORT

Case: FiniteBaseChangeRestrictionMateTransport. Lean 4.35.0 (`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`); Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`; source snapshot: `0676f555de6; finite_base_change_restriction_mate_transport`. Kernel source checksum: `8982321f70352a7c775c77e66e2f25dbf71ea9de7fe978fffb8f600862b7d566` (instrumented `type_checker.cpp` used by the READY build). Root conversion ID: `FB-hb-49-v1`.

## 1. Root

Kernel check of dependent proof argument 49 (`hb`) of `transport_from_unit` after 48 category, functor, equivalence and mate arguments. Both types are `forall M : FiniteModules A X'` squares; the first raw difference is `Scheme.ProEt X` versus `Site .ordinary X` under `ProjectionRestriction.Mod`. The root probe has 4,000,000 heartbeats and ends in `sorry` after the checked application.

Immutable probe: `probes/anatomy/original-ApplicationOnly.lean`. The raw left/right expressions and local context are recorded in `probes/HeadAudit.lean`. Release diagnostic run: 10:06.59 wall, 604.95 s user CPU, 23966284 KB peak RSS. Separate plain run: 10:43.24 wall and 23963280 KB RSS. Counters-only: 813.972 s root wall; 813.896 s comparison-exclusive (100.0%); 0.076 s WHNF-exclusive (0.0%). Whole-file counters run: 15:11.73 wall. Detailed trace root: 894.535 s; whole-file trace run: 16:49.59 wall, 35101408 KB RSS. The root result is success.

## 2. Reduction cost

WHNF requests 47,989; exclusive WHNF time 0.076 s. Delta events 339,228,680, nested Delta timer 23.237 s; Beta 143,602,888, Iota 0, Zeta 488,066, projection 19,746,683. Per-operation Beta/Iota/Zeta/projection exclusive times are not exposed. Top Delta heads by direct timed span in the trace (each span can overlap the comparison/WHNF partition):

| Constant | Unfolds | Delta ms |
|---|---:|---:|
| `DFunLike.coe` | 39,492,844 | 6549.888 |
| `AlgebraicGeometry.Scheme.Hom.toLRSHom` | 39,492,532 | 3663.354 |
| `AlgebraicGeometry.LocallyRingedSpace.Hom.toHom` | 39,492,370 | 3000.078 |
| `AlgebraicGeometry.Scheme.Hom.toLRSHom'` | 39,492,532 | 2013.606 |
| `AlgebraicGeometry.PresheafedSpace.Hom.base` | 39,492,368 | 1772.095 |
| `ContinuousMap.toFun` | 39,492,362 | 1616.056 |
| `Function.comp` | 39,492,364 | 1604.571 |
| `TopCat.Hom.hom'` | 39,492,368 | 1588.053 |

## 3. Recursive comparison cost

Total 239,340,712 calls: 68,714,993 successful, 170,625,719 failed/stuck/exception; max depth 87. Comparison-exclusive time 813.896 s. Branch counts: quick 68,971,032, quick_reduced 134,979, proof_irrelevance 3,293, lazy_delta 19,747,209, projection 3,415, second_whnf 840, application 2,464, failure 150,477,480.

Depth histogram: 65 buckets in the trace; `depth>=64` is grouped by 64-level buckets. Fan-out histogram: 19 buckets, 89,406,853 leaves, 138,678,112 single-child calls, 11,255,747 multi-child calls; maximum recorded bucket 21. Full depth, fan-out and kind-pair histograms are in `probes/anatomy/logs/original-ApplicationOnly.trace.stderr`. The Kernel patch records child heads and child counts, but not argument/field paths or descendant counts per top child.

Top 20 children by **trace-mode** exclusive time (parent ID, depth, heads, children, exclusive/inclusive/reduction time are preserved verbatim):

```text
ANATOMY child=193060502 parent=193060501 depth=72 children=1 left=DFunLike.coe right=DFunLike.coe exclusive_ms=10307.027 inclusive_ms=10307.122 reduction_ms=0.000
ANATOMY child=95001882 parent=95001881 depth=61 children=9 left=Eq.ndrec right=Eq.ndrec exclusive_ms=4824.890 inclusive_ms=4835.933 reduction_ms=0.000
ANATOMY child=46713967 parent=46713966 depth=74 children=1 left=DFunLike.coe right=DFunLike.coe exclusive_ms=2067.892 inclusive_ms=2067.982 reduction_ms=0.000
ANATOMY child=22935088 parent=22935087 depth=65 children=9 left=Eq.ndrec right=Eq.ndrec exclusive_ms=972.980 inclusive_ms=982.723 reduction_ms=0.000
ANATOMY child=11225481 parent=11225480 depth=72 children=1 left=DFunLike.coe right=DFunLike.coe exclusive_ms=447.468 inclusive_ms=447.482 reduction_ms=0.000
ANATOMY child=233513416 parent=233513415 depth=63 children=9 left=Eq.ndrec right=Eq.ndrec exclusive_ms=349.879 inclusive_ms=363.109 reduction_ms=0.000
ANATOMY child=5458873 parent=5458872 depth=59 children=4 left=Eq right=Eq exclusive_ms=210.584 inclusive_ms=210.590 reduction_ms=0.000
ANATOMY child=4935952 parent=4935951 depth=70 children=1 left=DFunLike.coe right=DFunLike.coe exclusive_ms=210.218 inclusive_ms=210.326 reduction_ms=0.000
ANATOMY child=111529907 parent=111529882 depth=67 children=4 left=5 right=5 exclusive_ms=142.128 inclusive_ms=152.584 reduction_ms=0.000
ANATOMY child=138778105 parent=138778104 depth=62 children=9 left=Eq.ndrec right=Eq.ndrec exclusive_ms=138.447 inclusive_ms=148.913 reduction_ms=0.000
ANATOMY child=2619264 parent=2619263 depth=70 children=1 left=DFunLike.coe right=DFunLike.coe exclusive_ms=100.238 inclusive_ms=100.322 reduction_ms=0.000
ANATOMY child=2424937 parent=2424933 depth=68 children=10 left=ContinuousMap.comp right=ContinuousMap.comp exclusive_ms=98.711 inclusive_ms=98.937 reduction_ms=0.000
ANATOMY child=122509372 parent=122509371 depth=66 children=4 left=Eq right=Eq exclusive_ms=66.009 inclusive_ms=66.042 reduction_ms=0.000
ANATOMY child=66681880 parent=66681855 depth=67 children=4 left=5 right=5 exclusive_ms=65.688 inclusive_ms=75.850 reduction_ms=0.000
ANATOMY child=51464449 parent=51464424 depth=66 children=4 left=5 right=5 exclusive_ms=65.246 inclusive_ms=75.853 reduction_ms=0.000
ANATOMY child=1221077 parent=1221076 depth=71 children=1 left=DFunLike.coe right=DFunLike.coe exclusive_ms=47.536 inclusive_ms=47.614 reduction_ms=0.000
ANATOMY child=1188569 parent=1188568 depth=72 children=1 left=DFunLike.coe right=DFunLike.coe exclusive_ms=47.487 inclusive_ms=47.595 reduction_ms=0.000
ANATOMY child=55973323 parent=55973322 depth=66 children=4 left=Eq right=Eq exclusive_ms=30.223 inclusive_ms=30.249 reduction_ms=0.000
ANATOMY child=31169679 parent=31169678 depth=63 children=9 left=Eq.ndrec right=Eq.ndrec exclusive_ms=27.690 inclusive_ms=37.414 reduction_ms=0.000
ANATOMY child=21877769 parent=21877768 depth=58 children=5 left=CategoryTheory.Limits.WidePullbackShape.wideCospan.match_1 right=CategoryTheory.Limits.WidePullbackShape.wideCospan.match_1 exclusive_ms=26.002 inclusive_ms=36.294 reduction_ms=0.000
```

## 4. Dependent and proof-type cost

Pi-domain comparison events 686; proof-irrelevance branch entries 3,293; proposition comparisons 3,293. The patch's proposition timer is 828.220 s, but it is inclusive/overlapping (and can exceed root wall), so it cannot be a cost-profile share or a measure of time before proof irrelevance. Instantiated binder, data-field, and proof-type exclusive times are not separately reported.

## 5. Repeated work

Trace captured 5,000,000 ordered expression-node pairs: 1,465,891 distinct exact pairs, 3,534,109 repeated exact entries, and 455,104 raw-hash structural groups. Repeated sampled calls accumulated 6.144 s exclusive time in trace mode. Capture is capped at 5,000,000 calls; numbers are sample-only if total calls exceed this. Context identity, reversed-pair tracking, top repeated groups, and actual cache-hit/miss behavior are unavailable. Zero cache counters in this patch do not prove absence of Kernel caching.

## 6. Memory

Release diagnostic peak RSS: 23966284 KB; instrumented trace whole-file peak RSS: 35101408 KB. Expr allocation counts/bytes, live bytes, DAG sharing, GC counts/time, and phase-specific memory attribution are unavailable. RSS is a process proxy, not an allocation cost share.

## 7. Cost profile

B (recursive comparison dominated): 239.34 million calls, 170.63 million failed calls, 87 maximum depth, and effectively all exclusive root time in comparison outside the instrumented WHNF span. The large fan-out total comes from repeated, mostly narrow subtrees.

Only comparison-exclusive and outer WHNF-exclusive timers form the reported root partition. Delta timing, proposition timing, and repeated-pair timing are nested or overlapping and must not be added. The patch charges bookkeeping overhead to calls; trace-mode top-child spikes can include pair-map growth and are qualitative. No separate instrumentation-overhead or other-Kernel category is measured at this root. Direct Delta time lacks left/right attribution.

## 8. Control comparison

The exact-proposition transport control checks in 4.40 s baseline whole-file time; with threshold zero every recorded control root is shorter than 100 ms. A separate `Site .ordinary X = X.ProEt` check is only a source-shape control and cannot time argument 49.

Control probe `probes/anatomy/aligned-TransportHB.lean`: release 0:04.40 wall, 2372056 KB RSS; largest threshold-zero instrumented root 164.117 ms and 19,783 calls. This is the largest root in the control file, not a stable cross-file conversion ID.

## 9. Conclusion

The expensive proposition check expands into a huge recursive comparison tree. The 339.23 million Delta events take 23.237 s on an overlapping timer, far less than the 813.972 s root; their count does not make the root reduction-dominated. The exact costly pair after `Site` exposure is not identified by the available top-head trace.

Measured claims are the release diagnostic, counters-only, and trace numbers above. Inferences about the semantic path rely on the preserved raw expression audit. Trace top-20 paths, per-child repeat counts, exact allocation costs, and a non-overlapping dependent/proof-type split are limitations of the supplied instrumentation.
