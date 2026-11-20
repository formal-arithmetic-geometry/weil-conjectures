# DEF EQ COST ANATOMY REPORT

Case: ImageHomCounit. Lean 4.35.0 (`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`); Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`; source snapshot: `212f97dd22a; imageHomIso_counit`. Kernel source checksum: `8982321f70352a7c775c77e66e2f25dbf71ea9de7fe978fffb8f600862b7d566` (instrumented `type_checker.cpp` used by the READY build). Root conversion ID: `IHC-final-exact-v1`.

## 1. Root

Final inferred-type/declared-type check at `exact h`: the inferred `conjugateEquiv_counit` equality uses raw `DerivedCategory (Sheaf ...)`, whereas the goal uses `DerivedCategoryModule` in `Quiver.Hom` and both composition sides.

Immutable probe: `probes/anatomy/original-FinalExact.lean`. The raw left/right expressions and local context are recorded in `probes/HeadAudit.lean`. Release diagnostic run: 0:57.03 wall, 55.92 s user CPU, 7522312 KB peak RSS. Separate plain run: 1:23.81 wall and 7522320 KB RSS. Counters-only: 73.084 s root wall; 37.145 s comparison-exclusive (50.8%); 35.939 s WHNF-exclusive (49.2%). Whole-file counters run: 1:35.56 wall. Detailed trace root: 106.008 s; whole-file trace run: 2:10.32 wall, 10305964 KB RSS. The root result is success.

## 2. Reduction cost

WHNF requests 20,993,747; exclusive WHNF time 35.939 s. Delta events 12,392,541, nested Delta timer 1.256 s; Beta 12,199,665, Iota 4, Zeta 346,213, projection 2,075,714. Per-operation Beta/Iota/Zeta/projection exclusive times are not exposed. Top Delta heads by direct timed span in the trace (each span can overlap the comparison/WHNF partition):

| Constant | Unfolds | Delta ms |
|---|---:|---:|
| `CategoryTheory.Functor.obj` | 603,417 | 165.828 |
| `HAdd.hAdd` | 842,356 | 114.652 |
| `DFunLike.coe` | 423,869 | 109.414 |
| `AddMonoid.toAdd` | 573,668 | 62.790 |
| `instHAdd` | 387,700 | 58.596 |
| `HSMul.hSMul` | 388,440 | 56.796 |
| `AddCommMagma.toAdd` | 348,924 | 51.057 |
| `AddGroup.toSubNegMonoid` | 365,204 | 49.816 |

## 3. Recursive comparison cost

Total 6,359,958 calls: 6,359,958 successful, 0 failed/stuck/exception; max depth 204. Comparison-exclusive time 37.145 s. Branch counts: quick 3,089,993, quick_reduced 66,571, proof_irrelevance 121,496, lazy_delta 21,344, projection 1,370,691, second_whnf 511,395, application 1,178,468.

Depth histogram: 67 buckets in the trace; `depth>=64` is grouped by 64-level buckets. Fan-out histogram: 20 buckets, 3,114,346 leaves, 1,899,299 single-child calls, 1,346,313 multi-child calls; maximum recorded bucket 28. Full depth, fan-out and kind-pair histograms are in `probes/anatomy/logs/original-FinalExact.trace.stderr`. The Kernel patch records child heads and child counts, but not argument/field paths or descendant counts per top child.

Top 20 children by **trace-mode** exclusive time (parent ID, depth, heads, children, exclusive/inclusive/reduction time are preserved verbatim):

```text
ANATOMY child=4050445 parent=4050444 depth=156 children=3 left=Add.add right=Add.add exclusive_ms=683.358 inclusive_ms=683.781 reduction_ms=0.122
ANATOMY child=4378684 parent=4378683 depth=170 children=3 left=Add.add right=Add.add exclusive_ms=666.802 inclusive_ms=667.139 reduction_ms=0.032
ANATOMY child=2156198 parent=2156197 depth=152 children=14 left=LinearMap.mk right=LinearMap.mk exclusive_ms=314.481 inclusive_ms=318.948 reduction_ms=0.001
ANATOMY child=4560266 parent=4560217 depth=159 children=4 left=AddCommGroup.toAddCommMonoid right=AddCommGroup.toAddCommMonoid exclusive_ms=313.419 inclusive_ms=313.763 reduction_ms=0.007
ANATOMY child=1990804 parent=1990801 depth=155 children=1 left=HAdd.hAdd right=HAdd.hAdd exclusive_ms=268.709 inclusive_ms=269.316 reduction_ms=0.056
ANATOMY child=2240412 parent=2240409 depth=163 children=2 left=DFunLike.coe right=DFunLike.coe exclusive_ms=149.615 inclusive_ms=149.678 reduction_ms=0.027
ANATOMY child=1062132 parent=1062131 depth=168 children=3 left=SMul.smul right=SMul.smul exclusive_ms=122.825 inclusive_ms=123.201 reduction_ms=0.098
ANATOMY child=976710 parent=976709 depth=162 children=6 left=ModuleCat.Hom._mkInternal right=ModuleCat.Hom._mkInternal exclusive_ms=115.142 inclusive_ms=119.021 reduction_ms=0.003
ANATOMY child=1098592 parent=1098591 depth=172 children=3 left=Add.add right=Add.add exclusive_ms=58.487 inclusive_ms=58.867 reduction_ms=0.015
ANATOMY child=477477 parent=477476 depth=180 children=1 left=ModuleCat.proj right=ModuleCat.proj exclusive_ms=53.320 inclusive_ms=53.336 reduction_ms=0.003
ANATOMY child=523247 parent=523246 depth=172 children=4 left=AddSemigroup.mk right=AddSemigroup.mk exclusive_ms=51.593 inclusive_ms=51.903 reduction_ms=0.001
ANATOMY child=536213 parent=536212 depth=171 children=3 left=Add.add right=Add.add exclusive_ms=26.180 inclusive_ms=26.304 reduction_ms=0.013
ANATOMY child=231569 parent=231568 depth=161 children=1 left=Add.proj right=Add.proj exclusive_ms=25.544 inclusive_ms=25.550 reduction_ms=0.000
ANATOMY child=257791 parent=257787 depth=175 children=4 left=Eq right=Eq exclusive_ms=24.595 inclusive_ms=24.777 reduction_ms=0.001
ANATOMY child=257944 parent=251796 depth=142 children=1 left=Function.Injective.addMonoid._proof_3 right=Function.Injective.addMonoid._proof_3 exclusive_ms=12.464 inclusive_ms=23.394 reduction_ms=0.002
ANATOMY child=127195 parent=127192 depth=168 children=1 left=HAdd.hAdd right=HAdd.hAdd exclusive_ms=10.932 inclusive_ms=11.124 reduction_ms=0.014
ANATOMY child=110511 parent=110510 depth=154 children=1 left=AddGroup.proj right=AddGroup.proj exclusive_ms=10.593 inclusive_ms=10.641 reduction_ms=0.006
ANATOMY child=122761 parent=122760 depth=174 children=3 left=Add.add right=Add.add exclusive_ms=5.295 inclusive_ms=5.452 reduction_ms=0.026
ANATOMY child=63061 parent=63027 depth=131 children=8 left=CategoryTheory.CategoryStruct.comp right=CategoryTheory.CategoryStruct.comp exclusive_ms=5.147 inclusive_ms=5.390 reduction_ms=0.006
ANATOMY child=50896 parent=50895 depth=171 children=0 left=AddMonoid.proj right=AddMonoid.proj exclusive_ms=5.088 inclusive_ms=5.090 reduction_ms=0.002
```

## 4. Dependent and proof-type cost

Pi-domain comparison events 265,526; proof-irrelevance branch entries 121,496; proposition comparisons 121,496. The patch's proposition timer is 335.396 s, but it is inclusive/overlapping (and can exceed root wall), so it cannot be a cost-profile share or a measure of time before proof irrelevance. Instantiated binder, data-field, and proof-type exclusive times are not separately reported.

## 5. Repeated work

Trace captured 5,000,000 ordered expression-node pairs: 3,355,551 distinct exact pairs, 1,644,449 repeated exact entries, and 2,607,175 raw-hash structural groups. Repeated sampled calls accumulated 0.686 s exclusive time in trace mode. Capture is capped at 5,000,000 calls; numbers are sample-only if total calls exceed this. Context identity, reversed-pair tracking, top repeated groups, and actual cache-hit/miss behavior are unavailable. Zero cache counters in this patch do not prove absence of Kernel caching.

## 6. Memory

Release diagnostic peak RSS: 7522312 KB; instrumented trace whole-file peak RSS: 10305964 KB. Expr allocation counts/bytes, live bytes, DAG sharing, GC counts/time, and phase-specific memory attribution are unavailable. RSS is a process proxy, not an allocation cost share.

## 7. Cost profile

F (mixed): comparison and WHNF each account for about half of the measured root. Deep (maximum 204) with material width (many calls have two to four children).

Only comparison-exclusive and outer WHNF-exclusive timers form the reported root partition. Delta timing, proposition timing, and repeated-pair timing are nested or overlapping and must not be added. The patch charges bookkeeping overhead to calls; trace-mode top-child spikes can include pair-map growth and are qualitative. No separate instrumentation-overhead or other-Kernel category is measured at this root. Direct Delta time lacks left/right attribution.

## 8. Control comparison

Full inferred-target alignment retains the same proof and makes all recorded conversions shorter than 100 ms. One wrapper expansion retains the inner mismatch and increases the main root to 9,539,325 calls and 116.247 s (57.738 s comparison, 58.509 s WHNF).

Control probe `probes/anatomy/aligned-UniformInferred.lean`: release 0:02.70 wall, 2854288 KB RSS; largest threshold-zero instrumented root 16.251 ms and 2,881 calls. This is the largest root in the control file, not a stable cross-file conversion ID.

Additional control `restored-UnfoldWrapper`: 9,539,325 calls and 116.247 s in its largest counters-only root.

## 9. Conclusion

The expensive work is distributed through a large comparison/reduction tree after the outer wrapper mismatch; the recorded top children do not support one dominant semantic child. `Functor.obj` Delta is frequent but its measured direct Delta time is small relative to root time.

Measured claims are the release diagnostic, counters-only, and trace numbers above. Inferences about the semantic path rely on the preserved raw expression audit. Trace top-20 paths, per-child repeat counts, exact allocation costs, and a non-overlapping dependent/proof-type split are limitations of the supplied instrumentation.
