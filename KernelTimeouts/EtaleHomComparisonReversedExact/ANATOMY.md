# DEF EQ COST ANATOMY REPORT

Case: EtaleHomComparisonReversedExact. Lean 4.35.0 (`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`); Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`; source snapshot: `8ca2e912b93; etaleHomComparison_reversedExact_commShift_component`. Kernel source checksum: `8982321f70352a7c775c77e66e2f25dbf71ea9de7fe978fffb8f600862b7d566` (instrumented `type_checker.cpp` used by the READY build). Root conversion ID: `EH-hv-26-v1`.

## 1. Root

Kernel check of proof argument 26 (`hv`) of `derivedTensorHomShiftComparison_component` after the first 25 dependent arguments. The supplied `IsEtaleHomTranspose X φ M v` proposition meets an instantiated `forall K : DerivedCategory (Sheaf ...), ...` domain. The probe checks the application; its `sorry` is afterward.

Immutable probe: `probes/anatomy/original-ApplicationOnly.lean`. The raw left/right expressions and local context are recorded in `probes/HeadAudit.lean`. Release diagnostic run: 0:30.22 wall, 29.14 s user CPU, 5552900 KB peak RSS. Separate plain run: 0:49.21 wall and 5552960 KB RSS. Counters-only: 36.191 s root wall; 18.707 s comparison-exclusive (51.7%); 17.484 s WHNF-exclusive (48.3%). Whole-file counters run: 0:49.13 wall. Detailed trace root: 51.663 s; whole-file trace run: 1:11.56 wall, 7067172 KB RSS. The root result is success.

## 2. Reduction cost

WHNF requests 10,497,410; exclusive WHNF time 17.484 s. Delta events 6,196,571, nested Delta timer 0.647 s; Beta 6,099,820, Iota 2, Zeta 173,150, projection 1,037,660. Per-operation Beta/Iota/Zeta/projection exclusive times are not exposed. Top Delta heads by direct timed span in the trace (each span can overlap the comparison/WHNF partition):

| Constant | Unfolds | Delta ms |
|---|---:|---:|
| `HAdd.hAdd` | 421,348 | 67.569 |
| `DFunLike.coe` | 211,908 | 62.835 |
| `HSMul.hSMul` | 194,232 | 35.628 |
| `CategoryTheory.Functor.obj` | 301,562 | 35.584 |
| `AddGroup.toSubNegMonoid` | 182,644 | 30.730 |
| `instHAdd` | 193,940 | 28.132 |
| `AddCommMagma.toAdd` | 174,540 | 27.496 |
| `SubNegMonoid.toAddMonoid` | 165,308 | 27.052 |

## 3. Recursive comparison cost

Total 3,180,470 calls: 3,180,470 successful, 0 failed/stuck/exception; max depth 111. Comparison-exclusive time 18.707 s. Branch counts: quick 1,545,487, quick_reduced 33,300, proof_irrelevance 60,717, lazy_delta 10,627, projection 685,494, second_whnf 255,588, application 589,257.

Depth histogram: 65 buckets in the trace; `depth>=64` is grouped by 64-level buckets. Fan-out histogram: 19 buckets, 1,557,660 leaves, 949,650 single-child calls, 673,160 multi-child calls; maximum recorded bucket 28. Full depth, fan-out and kind-pair histograms are in `probes/anatomy/logs/original-ApplicationOnly.trace.stderr`. The Kernel patch records child heads and child counts, but not argument/field paths or descendant counts per top child.

Top 20 children by **trace-mode** exclusive time (parent ID, depth, heads, children, exclusive/inclusive/reduction time are preserved verbatim):

```text
ANATOMY child=1984403 parent=1984402 depth=75 children=1 left=AddCommMonoid.proj right=AddCommMonoid.proj exclusive_ms=306.474 inclusive_ms=306.492 reduction_ms=0.016
ANATOMY child=2157032 parent=2157031 depth=71 children=3 left=Add.add right=Add.add exclusive_ms=289.268 inclusive_ms=289.404 reduction_ms=0.057
ANATOMY child=2216222 parent=2216221 depth=56 children=4 left=AddGroup.mk right=AddGroup.mk exclusive_ms=161.140 inclusive_ms=454.051 reduction_ms=0.002
ANATOMY child=1062782 parent=1062781 depth=82 children=1 left=Add.proj right=Add.proj exclusive_ms=116.694 inclusive_ms=116.918 reduction_ms=0.001
ANATOMY child=970410 parent=970409 depth=85 children=1 left=AddGroup.proj right=AddGroup.proj exclusive_ms=112.399 inclusive_ms=112.507 reduction_ms=0.013
ANATOMY child=1092580 parent=1092489 depth=78 children=7 left=AddHom.mk right=AddHom.mk exclusive_ms=67.038 inclusive_ms=69.446 reduction_ms=0.004
ANATOMY child=523809 parent=523808 depth=84 children=3 left=Add.add right=Add.add exclusive_ms=53.554 inclusive_ms=53.595 reduction_ms=0.033
ANATOMY child=471116 parent=471115 depth=82 children=1 left=SMul.smul right=SMul.smul exclusive_ms=53.517 inclusive_ms=57.008 reduction_ms=0.069
ANATOMY child=530233 parent=530232 depth=87 children=3 left=Add.add right=Add.add exclusive_ms=27.626 inclusive_ms=27.855 reduction_ms=0.015
ANATOMY child=258409 parent=258408 depth=74 children=3 left=Add.add right=Add.add exclusive_ms=25.178 inclusive_ms=25.432 reduction_ms=0.028
ANATOMY child=225122 parent=225121 depth=85 children=1 left=SubNegMonoid.proj right=SubNegMonoid.proj exclusive_ms=24.422 inclusive_ms=24.473 reduction_ms=0.002
ANATOMY child=253224 parent=253172 depth=74 children=7 left=AddHom.mk right=AddHom.mk exclusive_ms=12.041 inclusive_ms=14.330 reduction_ms=0.001
ANATOMY child=127842 parent=127838 depth=92 children=4 left=Eq right=Eq exclusive_ms=10.996 inclusive_ms=11.152 reduction_ms=0.001
ANATOMY child=104149 parent=104146 depth=74 children=1 left=DFunLike.coe right=DFunLike.coe exclusive_ms=10.831 inclusive_ms=11.231 reduction_ms=0.041
ANATOMY child=117107 parent=117106 depth=77 children=2 left=AddHom.toFun right=AddHom.toFun exclusive_ms=5.208 inclusive_ms=5.462 reduction_ms=0.052
ANATOMY child=63709 parent=63708 depth=89 children=3 left=Add.add right=Add.add exclusive_ms=4.747 inclusive_ms=5.687 reduction_ms=0.025
ANATOMY child=44570 parent=44564 depth=82 children=1 left=AddMonoid.add_assoc right=AddMonoid.add_assoc exclusive_ms=4.615 inclusive_ms=4.764 reduction_ms=0.001
ANATOMY child=49601 parent=49600 depth=85 children=3 left=Add.add right=Add.add exclusive_ms=2.263 inclusive_ms=2.417 reduction_ms=0.028
ANATOMY child=15272 parent=15264 depth=84 children=1 left=HAdd.hAdd right=HAdd.hAdd exclusive_ms=1.922 inclusive_ms=4.986 reduction_ms=0.012
ANATOMY child=31767 parent=31766 depth=80 children=1 left=AddCommSemigroup.proj right=AddCommSemigroup.proj exclusive_ms=1.895 inclusive_ms=2.080 reduction_ms=0.004
```

## 4. Dependent and proof-type cost

Pi-domain comparison events 132,807; proof-irrelevance branch entries 60,717; proposition comparisons 60,717. The patch's proposition timer is 148.892 s, but it is inclusive/overlapping (and can exceed root wall), so it cannot be a cost-profile share or a measure of time before proof irrelevance. Instantiated binder, data-field, and proof-type exclusive times are not separately reported.

## 5. Repeated work

Trace captured 3,180,470 ordered expression-node pairs: 2,133,978 distinct exact pairs, 1,046,492 repeated exact entries, and 1,658,099 raw-hash structural groups. Repeated sampled calls accumulated 0.399 s exclusive time in trace mode. Capture is capped at 5,000,000 calls; numbers are sample-only if total calls exceed this. Context identity, reversed-pair tracking, top repeated groups, and actual cache-hit/miss behavior are unavailable. Zero cache counters in this patch do not prove absence of Kernel caching.

## 6. Memory

Release diagnostic peak RSS: 5552900 KB; instrumented trace whole-file peak RSS: 7067172 KB. Expr allocation counts/bytes, live bytes, DAG sharing, GC counts/time, and phase-specific memory attribution are unavailable. RSS is a process proxy, not an allocation cost share.

## 7. Cost profile

F (mixed), with comparable comparison and WHNF costs; the root is an instantiated dependent proposition, deep to 111 and moderately wide.

Only comparison-exclusive and outer WHNF-exclusive timers form the reported root partition. Delta timing, proposition timing, and repeated-pair timing are nested or overlapping and must not be added. The patch charges bookkeeping overhead to calls; trace-mode top-child spikes can include pair-map growth and are qualitative. No separate instrumentation-overhead or other-Kernel category is measured at this root. Direct Delta time lacks left/right attribution.

## 8. Control comparison

Exact expected-proposition transport makes every recorded control root shorter than 100 ms. Exposing the named predicate alone keeps the main root at 3,179,834 calls and 36.007 s, virtually the original workload.

Control probe `probes/anatomy/aligned-TransportHV.lean`: release 0:03.40 wall, 3238628 KB RSS; largest threshold-zero instrumented root 83.711 ms and 7,014 calls. This is the largest root in the control file, not a stable cross-file conversion ID.

Additional control `restored-ExpandedHV`: 3,179,834 calls and 36.007 s in its largest counters-only root.

## 9. Conclusion

The costly work occurs while reconciling the fully instantiated proof proposition, including later data endpoints after the first binder-domain difference. The trace does not isolate a single responsible `Functor.obj` or `NatTrans.app` child.

Measured claims are the release diagnostic, counters-only, and trace numbers above. Inferences about the semantic path rely on the preserved raw expression audit. Trace top-20 paths, per-child repeat counts, exact allocation costs, and a non-overlapping dependent/proof-type split are limitations of the supplied instrumentation.
