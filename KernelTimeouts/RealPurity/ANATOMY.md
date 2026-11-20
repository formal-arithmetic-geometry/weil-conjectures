# DEF EQ COST ANATOMY REPORT

Case: RealPurity. Lean 4.35.0 (`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`); Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`; source snapshot: `e2d8b540cba; exists_isPunctuallyPureOfWeight_cokernel_detWeight`. Kernel source checksum: `8982321f70352a7c775c77e66e2f25dbf71ea9de7fe978fffb8f600862b7d566` (instrumented `type_checker.cpp` used by the READY build). Root conversion ID: `RPU-hreal-exact-v1`.

## 1. Root

Final `exact h` in local `hreal' : W.IsReal l P.obj.ρ ι` after the polynomial rewrites. The inferred and expected propositions first differ below `Polynomial.reverse`/`coeff` at `Field.toCommRing` versus `AlgebraicClosure.instCommRing` on both equality sides. Later proof work is discarded only after this root.

Immutable probe: `probes/anatomy/original-AfterHRealSorry.lean`. The raw left/right expressions and local context are recorded in `probes/HeadAudit.lean`. Release diagnostic run: 1:02.44 wall, 61.48 s user CPU, 5653788 KB peak RSS. Separate plain run: 0:59.74 wall and 5648900 KB RSS. Counters-only: 64.277 s root wall; 64.267 s comparison-exclusive (100.0%); 0.010 s WHNF-exclusive (0.0%). Whole-file counters run: 1:18.45 wall. Detailed trace root: 81.669 s; whole-file trace run: 1:34.86 wall, 7215260 KB RSS. The root result is a deterministic Kernel timeout, so these are partial-root numbers.

## 2. Reduction cost

WHNF requests 1,789; exclusive WHNF time 0.010 s. Delta events 33,163,711, nested Delta timer 1.905 s; Beta 10,357,567, Iota 4, Zeta 35,375, projection 1,430,971. Per-operation Beta/Iota/Zeta/projection exclusive times are not exposed. Top Delta heads by direct timed span in the trace (each span can overlap the comparison/WHNF partition):

| Constant | Unfolds | Delta ms |
|---|---:|---:|
| `DFunLike.coe` | 2,861,632 | 536.404 |
| `AlgebraicGeometry.Scheme.Hom.toLRSHom'` | 2,861,529 | 141.776 |
| `Function.comp` | 2,861,521 | 124.582 |
| `ContinuousMap.toFun` | 2,861,521 | 122.896 |
| `AlgebraicGeometry.PresheafedSpace.Hom.base` | 2,861,525 | 119.897 |
| `TopCat.Hom.hom'` | 2,861,525 | 119.587 |
| `AlgebraicGeometry.LocallyRingedSpace.Hom.toHom` | 2,861,527 | 113.604 |
| `AlgebraicGeometry.Scheme.Hom.toLRSHom` | 2,861,529 | 112.558 |

## 3. Recursive comparison cost

Total 17,340,901 calls: 4,977,891 successful, 12,363,010 failed/stuck/exception; max depth 93. Comparison-exclusive time 64.267 s. Branch counts: quick 4,996,769, quick_reduced 9,772, proof_irrelevance 214, lazy_delta 1,430,823, projection 60, second_whnf 85, application 44, failure 10,903,048, exception 86.

Depth histogram: 65 buckets in the trace; `depth>=64` is grouped by 64-level buckets. Fan-out histogram: 18 buckets, 6,477,438 leaves, 10,048,128 single-child calls, 815,335 multi-child calls; maximum recorded bucket 18. Full depth, fan-out and kind-pair histograms are in `probes/anatomy/logs/original-AfterHRealSorry.trace.stderr`. The Kernel patch records child heads and child counts, but not argument/field paths or descendant counts per top child.

Top 20 children by **trace-mode** exclusive time (parent ID, depth, heads, children, exclusive/inclusive/reduction time are preserved verbatim):

```text
ANATOMY child=11349981 parent=11349980 depth=84 children=1 left=DFunLike.coe right=DFunLike.coe exclusive_ms=442.832 inclusive_ms=442.969 reduction_ms=0.000
ANATOMY child=5583335 parent=5583334 depth=84 children=1 left=DFunLike.coe right=DFunLike.coe exclusive_ms=221.708 inclusive_ms=221.819 reduction_ms=0.000
ANATOMY child=4974996 parent=4974981 depth=85 children=1 left=ContinuousMap.proj right=Function.comp exclusive_ms=221.279 inclusive_ms=221.507 reduction_ms=0.000
ANATOMY child=2743773 parent=2743772 depth=85 children=1 left=DFunLike.coe right=DFunLike.coe exclusive_ms=102.007 inclusive_ms=102.122 reduction_ms=0.000
ANATOMY child=2449344 parent=2449320 depth=84 children=1 left=ContinuousMap.proj right=Function.comp exclusive_ms=100.715 inclusive_ms=100.924 reduction_ms=0.000
ANATOMY child=1205744 parent=1205743 depth=86 children=1 left=DFunLike.coe right=DFunLike.coe exclusive_ms=47.959 inclusive_ms=48.097 reduction_ms=0.000
ANATOMY child=1345582 parent=1345581 depth=86 children=1 left=DFunLike.coe right=DFunLike.coe exclusive_ms=47.825 inclusive_ms=47.945 reduction_ms=0.000
ANATOMY child=593228 parent=593224 depth=83 children=10 left=ContinuousMap.comp right=ContinuousMap.comp exclusive_ms=23.448 inclusive_ms=23.779 reduction_ms=0.000
ANATOMY child=656891 parent=656890 depth=85 children=1 left=DFunLike.coe right=DFunLike.coe exclusive_ms=22.656 inclusive_ms=22.676 reduction_ms=0.000
ANATOMY child=16719736 parent=16719735 depth=73 children=9 left=Eq.ndrec right=Eq.ndrec exclusive_ms=18.653 inclusive_ms=32.955 reduction_ms=0.000
ANATOMY child=13542058 parent=13542057 depth=76 children=9 left=Eq.ndrec right=Eq.ndrec exclusive_ms=11.036 inclusive_ms=23.954 reduction_ms=0.000
ANATOMY child=317848 parent=317847 depth=85 children=1 left=DFunLike.coe right=DFunLike.coe exclusive_ms=10.772 inclusive_ms=10.824 reduction_ms=0.000
ANATOMY child=291650 parent=291626 depth=84 children=1 left=ContinuousMap.proj right=Function.comp exclusive_ms=10.728 inclusive_ms=10.811 reduction_ms=0.000
ANATOMY child=6370646 parent=6370621 depth=77 children=4 left=5 right=5 exclusive_ms=9.328 inclusive_ms=32.033 reduction_ms=0.000
ANATOMY child=14693599 parent=14693598 depth=74 children=9 left=Eq.ndrec right=Eq.ndrec exclusive_ms=6.513 inclusive_ms=18.856 reduction_ms=0.000
ANATOMY child=8108269 parent=8108268 depth=74 children=9 left=Eq.ndrec right=Eq.ndrec exclusive_ms=5.846 inclusive_ms=18.072 reduction_ms=0.000
ANATOMY child=150939 parent=150938 depth=85 children=1 left=DFunLike.coe right=DFunLike.coe exclusive_ms=5.127 inclusive_ms=5.155 reduction_ms=0.000
ANATOMY child=143122 parent=142910 depth=83 children=8 left=AlgebraicGeometry.PresheafedSpace.Hom.proj right=CategoryTheory.CategoryStruct.comp exclusive_ms=5.094 inclusive_ms=5.582 reduction_ms=0.000
ANATOMY child=6741771 parent=6741770 depth=77 children=4 left=Eq right=Eq exclusive_ms=4.015 inclusive_ms=4.037 reduction_ms=0.000
ANATOMY child=3861513 parent=3861512 depth=77 children=9 left=Eq.ndrec right=Eq.ndrec exclusive_ms=2.662 inclusive_ms=16.569 reduction_ms=0.000
```

## 4. Dependent and proof-type cost

Pi-domain comparison events 34; proof-irrelevance branch entries 214; proposition comparisons 215. The patch's proposition timer is 68.684 s, but it is inclusive/overlapping (and can exceed root wall), so it cannot be a cost-profile share or a measure of time before proof irrelevance. Instantiated binder, data-field, and proof-type exclusive times are not separately reported.

## 5. Repeated work

Trace captured 5,000,000 ordered expression-node pairs: 1,454,427 distinct exact pairs, 3,545,573 repeated exact entries, and 451,846 raw-hash structural groups. Repeated sampled calls accumulated 10.206 s exclusive time in trace mode. Capture is capped at 5,000,000 calls; numbers are sample-only if total calls exceed this. Context identity, reversed-pair tracking, top repeated groups, and actual cache-hit/miss behavior are unavailable. Zero cache counters in this patch do not prove absence of Kernel caching.

## 6. Memory

Release diagnostic peak RSS: 5653788 KB; instrumented trace whole-file peak RSS: 7215260 KB. Expr allocation counts/bytes, live bytes, DAG sharing, GC counts/time, and phase-specific memory attribution are unavailable. RSS is a process proxy, not an allocation cost share.

## 7. Cost profile

B (recursive comparison dominated) for the partial root: 64.267 s comparison versus 0.010 s WHNF at the heartbeat timeout. The trace is narrow in fan-out but contains many repeated subtrees around depth 65-93.

Only comparison-exclusive and outer WHNF-exclusive timers form the reported root partition. Delta timing, proposition timing, and repeated-pair timing are nested or overlapping and must not be added. The patch charges bookkeeping overhead to calls; trace-mode top-child spikes can include pair-map growth and are qualitative. No separate instrumentation-overhead or other-Kernel category is measured at this root. Direct Delta time lacks left/right attribution.

## 8. Control comparison

Aligning both ring leaves leaves the deterministic timeout and essentially identical main-root counts: 17,340,901 calls, 12,363,010 failures, and 63.831 s versus 64.277 s counters-only original. Left-only alignment likewise retains 17,340,901 calls. The next raw data difference after both leaves is `Functor.obj` versus local `P`.

Control probe `probes/anatomy/aligned-AlignBothRing.lean`: release 0:58.43 wall, 5649104 KB RSS; largest threshold-zero instrumented root 63831.391 ms and 17,340,901 calls. This is the largest root in the control file, not a stable cross-file conversion ID.

Additional control `restored-AlignLeftRing`: 17,340,901 calls and 65.281 s in its largest counters-only root.

## 9. Conclusion

The first ring leaves are not sufficient to explain the timeout. Its internal signature almost exactly matches RealPushforward, including the `ContinuousMap`/`DFunLike.coe` top-head families. The dominant semantic pair beyond those heads is unlocated.

Measured claims are the release diagnostic, counters-only, and trace numbers above. Inferences about the semantic path rely on the preserved raw expression audit. Trace top-20 paths, per-child repeat counts, exact allocation costs, and a non-overlapping dependent/proof-type split are limitations of the supplied instrumentation.
