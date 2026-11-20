# Targeted DefEq Follow-up: Cross-Case Synthesis

This joins the two historical reference roots measured with READY2
(Lean 4.33.1) to the 15 current cases reported by P2 and T2. The current
case table below uses the final READY2 reruns, not the earlier anatomy
pass. P2 publishes trace comparison/reduction partitions; where T2's final
report publishes only the counters partition, that partition is labelled
explicitly. OrderedSpectralRawLattices has a trace-only root, so coverage
totals use 16 counter roots (two historical, 14 current). Two current rows
are partial timeout roots. The measurements are Kernel conversion spans,
not whole files or theorem builds. Companion records are the two historical
`EXPERIMENTS-AD.md` reports, `PerfIssues/AD-REPORT.md`, and
`KernelTimeouts/AD-REPORT.md`.

| Case | Root s | WHNF s | Compare s | Calls | Depth | Fan-out evidence | Exact repeats | Allocation |
| --- | ---: | ---: | ---: | ---: | ---: | --- | --- | --- |
| Slow Derived Tensor | 42.201 | 19.207 | 22.994 | 6,269,622 | 96 | max 28 | 1,666,128 / 5m | 239.0m C++ Expr outputs |
| Derived-Completion Cone | 103.297 | 51.826 | 51.471 | 12,220,822 | 111 | max 28 | 1,583,761 / 5m | 603.0m C++ Expr outputs |

The first table is retained for the two historical reference roots. Exact-
pair capture is capped at five million calls and omits local context. The
final READY2 values for all current cases are authoritative in the table
below.

## Final READY2 current cases

The `root` column gives trace wall time followed by the counters root when
both were published. P2's comparison/reduction column is trace-exclusive
followed by the counter split; T2's final report published the counter split
only. Dependent share is the dependent-comparison timer divided by the
corresponding comparison-exclusive timer. Expr counts/bytes are constructor
proxies; RSS/commit is a process proxy. Path samples are inclusive and are
not additive.

| Case | Root s | Compare / reduction s | Calls | Depth | Dependent share | Expr proxy; RSS/commit proxy | Top measured path |
| --- | ---: | ---: | ---: | ---: | ---: | --- | --- |
| NativePullTensor | 41.489 / 22.407 | 22.845 / 18.644 trace; 15.131 / 7.276 counter | 2,685,580 | 81 | 67.4% | 97,609,480 / 3,325,394,512 B; +1.832 GB | `Functor.comp` -> `Functor.obj`, 22.768/18.720 s |
| PR1556 | 92.750 / 61.051 | 48.035 / 44.715 trace; 29.147 / 31.904 counter | 6,670,198 | 213 | 80.0% | 298,357,470 / 9,970,769,744 B; +103 MB | `CategoryStruct.comp` -> `NatTrans.app`, 76.274 s |
| PR1625 | 142.415 / 97.208 | 82.162 / 60.253 trace; 49.661 / 47.548 counter | 11,757,788 | 125 | 76.2% | 438,450,718 / 14,677,924,016 B; +5.443 GB | outer `CategoryStruct.comp`/`NatTrans.app`, 141.309 s |
| PR1563 | 28.699 / 22.419 | 15.785 / 12.914 trace; 10.744 / 11.675 counter | 2,573,989 | 95 | 79.6% | 112,996,826 / 3,776,404,760 B; +0 | nested `CategoryStruct.comp`/`DFunLike.coe`, 25.813 s |
| PR1627 | 40.766 / 29.197 | 23.912 / 16.854 trace; 15.744 / 13.453 counter | 10,904,899 | 61 | 98.5% | 151,676,221 / 5,085,228,440 B; +16.7 MB | generated `Endofunctor.Algebra.a`, 9.560 s; two `frobeniusPullback` branches |
| PR1624 | 66.440 / 52.710 | 37.378 / 29.062 trace; 26.154 / 26.556 counter | 6,598,545 | 88 | 80.2% | 293,181,229 / 9,796,728,600 B; +4.621 GB | `singleFunctor` proof/proposition, 2.421 s |
| PR2122 | 24.154 / 18.025 | 12.314 / 11.840 trace; 7.779 / 10.246 counter | 2,227,198 | 93 | 69.4% | 84,397,734 / 2,810,518,408 B; +1.528 GB | `ModuleCat.carrier` -> `AddCommGrpCat.carrier`, 192 ms sample |
| EtaleHom | 31.825 / 24.140 | 12.301 / 11.839 counter | 3,180,470 | 111 | 80.2% | 140,620,668 / 4,699,706,856 B; +2.374 GB | `DFunLike.coe` -> `NatTrans.app`, 31.817 s; `tensorLeft`, 14.395 s |
| FiniteBaseChange | 776.225 / 661.952 | 661.896 / 0.056 counter | 239,340,712 | 87 | 99.6% | 2,960,140,990 / 96,645,705,328 B; +22.042 GB | `CategoryStruct.comp` -> `LinearMap.comp` -> `PresheafOfModules.Hom.proj` -> `NatTrans.app`, 776.096 s |
| F66Adj | 38.829 / 29.544 | 15.058 / 14.486 counter | 3,897,905 | 121 | 80.4% | 170,987,170 / 5,714,525,816 B; +2.871 GB | nested `DFunLike.coe`/`NatTrans.app`, 34.886 s |
| ImageHomCounit | 62.200 / 50.730 | 25.076 / 25.655 counter | 6,359,958 | 204 | 80.9% | 281,230,787 / 9,398,990,560 B; +4.752 GB | `Functor.map` -> `NatTrans.app` -> `DFunLike.coe`, 62.183 s |
| IntegralComparison | 88.313 / 73.839 | 44.816 / 29.024 counter | 9,426,253 | 183 | 89.7% | 438,986,428 / 14,632,433,896 B; +5.418 GB | nested `CategoryStruct.comp` -> `NatTrans.app`, 46.686 s descendant; 88.312 s chain |
| RealPurity (partial) | 70.041 / 53.956 | 53.949 / 0.007 counter | 17,310,168 | 93 | 99.6% | 280,888,851 / 9,127,445,872 B; +1.582 GB | `DFunLike.coe` -> `Complex.re` -> `Matrix.charmatrix`, 70.033 s |
| RealPushforward (partial) | 68.258 / 52.072 | 52.069 / 0.003 counter | 17,340,236 | 91 | 99.6% | 281,349,193 / 9,142,377,040 B; +1.587 GB | `Matrix.charmatrix` -> nested `DFunLike.coe`, 68.253 s |
| OrderedSpectralRawLattices | 51.962 trace-only | 51.938 / 0.024 counter-style partition | 18,944,709 | N/A | 99.7% | 213,249,957 / 6,975,943,792 B; +956 MB | `Exists`/`Quiver.Hom` -> `Functor.obj`/`Mod.X`, 51.909 s |

## READY2 reruns

The companion reruns completed against `READY2-4.35.0`. T2's records now
contain READY2 counters and traces for EtaleHom, FiniteBaseChange, F66Adj,
ImageHomCounit, IntegralComparison, RealPurity, RealPushforward, and
OrderedSpectralRawLattices; P2's completed logs cover NativePullTensor,
PR1556, PR1625, PR1563, PR1627, PR1624, and PR2122. These reruns preserve
the first-pass root mechanisms and add component paths, disjoint dependent
timers, and Expr/RSS proxies. The table keeps one comparable selected root
per case; controls and trace-only roots are reported in the companion
`AD-REPORT.md` files rather than mixed into the coverage totals.

## Measured cost coverage

Across the 16 selected counter roots, 1,394.749 s of Kernel conversion
time was measured. Exclusive recursive comparison accounts for 1,093.991 s
(78.4%); outer WHNF/reduction accounts for 300.759 s (21.6%). Ordered-
SpectralRawLattices is excluded because its READY2 result is trace-only.
FiniteBaseChange alone contributes 661.952 s (47.5%), so these are
workload-weighted totals rather than a typical-case profile. Within the two historical
roots, disjoint dependent-labelled comparison/reduction is 112.941 s
and proposition-labelled work is 32.555 s, together 145.496 s of their
145.498 s roots. The remaining 2 ms is unlabelled/rounding. A binder
body nested inside a proposition is assigned to dependent; this is a
path classification, not a claim that domain *checking* consumed that
time. READY2 now exposes these labels for the current cases, but the
controls and multiple roots are not combined into a project-wide exclusive
coverage figure here.

No allocation-time or GC-time share can be computed. READY2 does provide
an Expr-constructor proxy for every current root: counts range from
84,397,734 (PR2122) to 2,960,140,990 (FiniteBaseChange), with the bytes
and RSS/commit deltas shown in the current-case table. The metric excludes
Lean-generated constructors, other runtime objects, retained live bytes,
and allocator time. RSS/commit therefore cannot establish an
allocation-dominated classification. No measured root is confirmed
allocation dominated.

## Mechanisms and cases

1. **Reduction dominance:** 0 of 16 selected counter roots is
   unambiguously reduction dominated. PR2122 (56.8% reduction), Cone
   (50.2%), and the other mixed roots show that a large WHNF partition is
   not sufficient to identify a reduction-only cause. The historical high
   Delta counts are cheap direct unfolds: 0.802 s Tensor and 2.081 s Cone.
   RealPushforward remains comparison heavy despite its polynomial
   representation control completing quickly.
2. **Recursive comparison dominance:** FiniteBaseChange, RealPurity,
   and RealPushforward are above 99.9% comparison-exclusive (3 of 16,
   767.914 s or 55.0% of measured root time). The latter two are partial
   timeout roots. The other 13 roots (626.835 s) are mixed to varying
   degrees; IntegralComparison is comparison weighted but still spends
   44.816 s in its final counter partition.
3. **Dependent/proposition cost:** The final READY2 dependent-comparison
   shares are 67.4--98.5% for P2's seven cases and 80.2--99.7% for T2's
   eight cases (the OrderedSpectral value is trace-only). The timer is a
   nested diagnostic, not an exclusive project-wide partition. The
   historical binder-instantiation timer totals only 0.714 s; the body and
   generated type comparisons are the expensive part.
4. **Width and depth:** Seven of the 16 counter roots exceed depth 100:
   Cone, EtaleHom, F66Adj, ImageHomCounit, IntegralComparison, PR1556, and
   PR1625. The final component paths show different width signatures, from
   the repeated `NatTrans.app` chain in FiniteBaseChange to the two
   generated `frobeniusPullback` branches in PR1627. No common numeric
   threshold makes a defensible project-wide `high fan-out` count.
5. **Repetition:** The historical and P2 traces contain many repeated
   exact expression-node pairs, but no root is proven repeated-pair
   dominated. Immediate repeated-pair time is small in the historical
   captures and ranges from about 0.5% to 11.2% in P2's diagnostics;
   descendant replay and context identity remain unmeasured.
6. **Historical/current recurrence:** Tensor's expensive
   `HasLeftDerivedFunctor₂` type enters sibling `CategoryStruct.comp`,
   `DFunLike.coe`, and `NatTrans.app` subtrees. Cone's `tensorLeft` path
   enters the same head families. Final READY2 paths repeat `NatTrans.app`
   in PR1556, PR1625, F66Adj, ImageHomCounit, IntegralComparison, and
   EtaleHom; `DFunLike.coe`/`Matrix.charmatrix` dominates both real-number
   partial roots, and generated dependent fields dominate PR1627. This is
   a recurring operation shape, not proof that the same exact ordered pair
   or cache entry occurs across cases.

## Answers to AD.md §7 and §8

**Exact expensive components (question 1).** Tensor trace assigns
37.565 s and 16.437 s to two sibling arguments within one
`HasLeftDerivedFunctor₂` proposition type; these account for 97.6% of its
55.322 s trace root. Cone trace assigns 105.417 s (85.2% of its 123.761 s
trace root) to `NatTrans.app` descendants of a dependent
`tensorLeft`/`CategoryStruct.comp` comparison. The final current paths put
the same shape in PR1556 (76.274 s), PR1625 (141.309 s), FiniteBaseChange
(776.096 s), and ImageHomCounit (62.183 s), while RealPurity and
RealPushforward are dominated by `Matrix.charmatrix`/`DFunLike.coe`.
These path-prefix times are inclusive samples and are not additive.

**Sharing versus reconstruction (question 2).** No valid three-way
B0/B1/B2 comparison at an unchanged historical root was established. The
Tensor READY2 validity rerun reproduced expensive independent-provider
roots (about 42--44 s) and a sub-threshold shared-binder path, but the
shared declaration adds an `MC` instance binder: its inferred/declared
type sizes are 2,283/3,917 versus 5,361/18,817 for the original. The
direct 0 ms meta checks therefore occur after the original conversion has
been removed. T2's earlier claim that this proves causal sharing is
rejected and its KernelTimeouts report is corrected. The Tensor record,
Cone controls, OrderedSpectral controls, and PR1627 controls all support
the same validity limitation. The project-wide sharing question remains
open.

**Dependent cost (question 3).** Direct instantiation is small in the
historical roots (0.392 s Tensor, 0.322 s Cone). Most measured time is in
recursive dependent-body and proposition-type subtrees reached after
instantiation. The final dependent timer shares (67.4--98.5% for P2 and
80.2--99.7% for T2) show that this pattern is widespread, while the
transport controls in EtaleHom, FiniteBaseChange, F66Adj, and ImageHomCounit
show causality at the whole proposition/endpoint level. The timers remain
nested, so they do not distinguish domain checking from body work alone.

**Recurrence (question 4).** Mixed reduction/comparison and deep generated
type comparisons recur in both historical cases and several current cases.
FiniteBaseChange and the RealPurity/RealPushforward partial roots form a
different, overwhelmingly recursive-comparison signature. Expr/RSS proxies
vary by orders of magnitude, but they are not allocation-time measurements
and do not establish allocation as the cause. No selected root supports a
simple `many Delta unfolds = expensive Delta` explanation. A valid
same-root provider matrix or source-level ablation of the specific inner
paths remains the next discriminating experiment.
