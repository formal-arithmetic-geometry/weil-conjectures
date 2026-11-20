# DEF EQ COST ANATOMY REPORT

Case: F66Adj. Lean 4.35.0 (`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`); Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`; source snapshot: `f66ad18a9ed; imageHomIso_naturality`. Kernel source checksum: `8982321f70352a7c775c77e66e2f25dbf71ea9de7fe978fffb8f600862b7d566` (instrumented `type_checker.cpp` used by the READY build). Root conversion ID: `F66-hR-39-v1`.

## 1. Root

Kernel check of proof argument 39 (`hR`) of `homIso_naturality_of_counit` after the first 38 dependent arguments. The supplied counit proposition has `Over.left (Over.mk f.left)` in its `DerivedCategoryModule` scheme argument; the expected proposition uses the local scheme variable. The probe checks the helper application and ends in `sorry` afterward.

Immutable probe: `probes/anatomy/original-ApplicationOnly.lean`. The raw left/right expressions and local context are recorded in `probes/HeadAudit.lean`. Release diagnostic run: 0:36.72 wall, 35.71 s user CPU, 5708728 KB peak RSS. Separate plain run: 1:04.67 wall and 5701108 KB RSS. Counters-only: 44.174 s root wall; 22.801 s comparison-exclusive (51.6%); 21.373 s WHNF-exclusive (48.4%). Whole-file counters run: 0:59.84 wall. Detailed trace root: 64.889 s; whole-file trace run: 1:27.78 wall, 7488828 KB RSS. The root result is success.

## 2. Reduction cost

WHNF requests 12,817,653; exclusive WHNF time 21.373 s. Delta events 7,555,566, nested Delta timer 0.767 s; Beta 7,445,839, Iota 2, Zeta 210,233, projection 1,260,111. Per-operation Beta/Iota/Zeta/projection exclusive times are not exposed. Top Delta heads by direct timed span in the trace (each span can overlap the comparison/WHNF partition):

| Constant | Unfolds | Delta ms |
|---|---:|---:|
| `CategoryTheory.Functor.obj` | 366,251 | 100.811 |
| `DFunLike.coe` | 257,296 | 69.842 |
| `HAdd.hAdd` | 511,564 | 69.514 |
| `AddMonoid.toAdd` | 348,388 | 37.883 |
| `HSMul.hSMul` | 235,848 | 34.775 |
| `AddCommMagma.toAdd` | 211,908 | 34.489 |
| `AddGroup.toSubNegMonoid` | 221,764 | 31.517 |
| `Add.add` | 511,564 | 29.014 |

## 3. Recursive comparison cost

Total 3,897,905 calls: 3,897,905 successful, 0 failed/stuck/exception; max depth 121. Comparison-exclusive time 22.801 s. Branch counts: quick 1,896,777, quick_reduced 40,428, proof_irrelevance 73,771, lazy_delta 24,677, projection 832,323, second_whnf 310,390, application 719,539.

Depth histogram: 65 buckets in the trace; `depth>=64` is grouped by 64-level buckets. Fan-out histogram: 21 buckets, 1,919,350 leaves, 1,145,484 single-child calls, 833,071 multi-child calls; maximum recorded bucket 28. Full depth, fan-out and kind-pair histograms are in `probes/anatomy/logs/original-ApplicationOnly.trace.stderr`. The Kernel patch records child heads and child counts, but not argument/field paths or descendant counts per top child.

Top 20 children by **trace-mode** exclusive time (parent ID, depth, heads, children, exclusive/inclusive/reduction time are preserved verbatim):

```text
ANATOMY child=1994048 parent=1994047 depth=76 children=1 left=Add.add right=Add.add exclusive_ms=322.842 inclusive_ms=329.004 reduction_ms=0.079
ANATOMY child=2164107 parent=2164104 depth=86 children=4 left=Eq right=Eq exclusive_ms=281.502 inclusive_ms=281.881 reduction_ms=0.003
ANATOMY child=2226803 parent=2226800 depth=92 children=2 left=DFunLike.coe right=DFunLike.coe exclusive_ms=155.613 inclusive_ms=155.788 reduction_ms=0.021
ANATOMY child=1066315 parent=1066314 depth=94 children=14 left=LinearMap.mk right=LinearMap.mk exclusive_ms=119.390 inclusive_ms=123.597 reduction_ms=0.001
ANATOMY child=976664 parent=976663 depth=71 children=1 left=HAdd.proj right=HAdd.proj exclusive_ms=115.868 inclusive_ms=120.208 reduction_ms=0.034
ANATOMY child=1089044 parent=1089043 depth=79 children=3 left=7 right=7 exclusive_ms=61.030 inclusive_ms=61.677 reduction_ms=0.000
ANATOMY child=525086 parent=525085 depth=107 children=1 left=AddSemigroup.toAdd right=AddSemigroup.toAdd exclusive_ms=52.763 inclusive_ms=53.128 reduction_ms=0.006
ANATOMY child=474835 parent=474825 depth=105 children=1 left=HSMul.hSMul right=HSMul.hSMul exclusive_ms=50.961 inclusive_ms=51.102 reduction_ms=0.044
ANATOMY child=527542 parent=527534 depth=84 children=2 left=6 right=6 exclusive_ms=25.864 inclusive_ms=29.589 reduction_ms=0.000
ANATOMY child=258425 parent=258424 depth=82 children=3 left=NSMul.nsmul right=NSMul.nsmul exclusive_ms=24.831 inclusive_ms=25.325 reduction_ms=0.009
ANATOMY child=227092 parent=227082 depth=59 children=1 left=AddCommGroup.add_comm right=AddCommGroup.add_comm exclusive_ms=23.927 inclusive_ms=24.223 reduction_ms=0.001
ANATOMY child=251787 parent=251786 depth=67 children=14 left=LinearMap.mk right=LinearMap.mk exclusive_ms=12.241 inclusive_ms=16.353 reduction_ms=0.001
ANATOMY child=126940 parent=126939 depth=80 children=1 left=SMul.smul right=SMul.smul exclusive_ms=10.546 inclusive_ms=11.027 reduction_ms=0.076
ANATOMY child=105636 parent=105635 depth=75 children=1 left=AddHom.proj right=AddHom.proj exclusive_ms=10.457 inclusive_ms=10.641 reduction_ms=0.003
ANATOMY child=115726 parent=115720 depth=58 children=1 left=AddMonoid.add_assoc right=AddMonoid.add_assoc exclusive_ms=5.174 inclusive_ms=5.316 reduction_ms=0.001
ANATOMY child=62554 parent=62551 depth=82 children=3 left=HAdd.hAdd right=HAdd.hAdd exclusive_ms=4.861 inclusive_ms=4.868 reduction_ms=0.007
ANATOMY child=45921 parent=45920 depth=70 children=3 left=SMul.smul right=SMul.smul exclusive_ms=4.401 inclusive_ms=4.652 reduction_ms=0.049
ANATOMY child=16518 parent=16515 depth=84 children=1 left=HSMul.hSMul right=HSMul.hSMul exclusive_ms=2.289 inclusive_ms=2.419 reduction_ms=0.025
ANATOMY child=30528 parent=30517 depth=67 children=2 left=Neg.neg right=Neg.neg exclusive_ms=2.119 inclusive_ms=2.177 reduction_ms=0.013
ANATOMY child=48477 parent=48476 depth=68 children=3 left=Add.add right=Add.add exclusive_ms=2.013 inclusive_ms=2.180 reduction_ms=0.011
```

## 4. Dependent and proof-type cost

Pi-domain comparison events 176,636; proof-irrelevance branch entries 73,771; proposition comparisons 73,771. The patch's proposition timer is 188.043 s, but it is inclusive/overlapping (and can exceed root wall), so it cannot be a cost-profile share or a measure of time before proof irrelevance. Instantiated binder, data-field, and proof-type exclusive times are not separately reported.

## 5. Repeated work

Trace captured 3,897,905 ordered expression-node pairs: 2,607,289 distinct exact pairs, 1,290,616 repeated exact entries, and 2,029,075 raw-hash structural groups. Repeated sampled calls accumulated 0.639 s exclusive time in trace mode. Capture is capped at 5,000,000 calls; numbers are sample-only if total calls exceed this. Context identity, reversed-pair tracking, top repeated groups, and actual cache-hit/miss behavior are unavailable. Zero cache counters in this patch do not prove absence of Kernel caching.

## 6. Memory

Release diagnostic peak RSS: 5708728 KB; instrumented trace whole-file peak RSS: 7488828 KB. Expr allocation counts/bytes, live bytes, DAG sharing, GC counts/time, and phase-specific memory attribution are unavailable. RSS is a process proxy, not an allocation cost share.

## 7. Cost profile

F (mixed), roughly equal structural-comparison and WHNF cost; depth 121 and material width. The root is an instantiated proof proposition, but proposition-type time is an overlapping timer.

Only comparison-exclusive and outer WHNF-exclusive timers form the reported root partition. Delta timing, proposition timing, and repeated-pair timing are nested or overlapping and must not be added. The patch charges bookkeeping overhead to calls; trace-mode top-child spikes can include pair-map growth and are qualitative. No separate instrumentation-overhead or other-Kernel category is measured at this root. Direct Delta time lacks left/right attribution.

## 8. Control comparison

Replacing only `hR` with the direct restriction-counit proof makes all recorded control roots shorter than 100 ms. Replacing only the preceding tensor-isomorphism argument leaves 3,901,014 calls and 44.295 s in the main root.

Control probe `probes/anatomy/aligned-ReplaceHR.lean`: release 0:03.50 wall, 2894520 KB RSS; largest threshold-zero instrumented root 26.484 ms and 2,881 calls. This is the largest root in the control file, not a stable cross-file conversion ID.

Additional control `restored-ReplaceTauQ`: 3,901,014 calls and 44.295 s in its largest counters-only root.

## 9. Conclusion

The proof argument representation is causal at the application level. The `Over.left` raw difference and later `NatTrans.app`/functor paths are not individually timed as semantic child components by this instrumentation.

Measured claims are the release diagnostic, counters-only, and trace numbers above. Inferences about the semantic path rely on the preserved raw expression audit. Trace top-20 paths, per-child repeat counts, exact allocation costs, and a non-overlapping dependent/proof-type split are limitations of the supplied instrumentation.
