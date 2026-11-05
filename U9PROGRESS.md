# K4c strategy 3, 2026-11-05

19:41 CST: Started from c6a69c87e on u9/K4c. Read README, shared experiments and NOTES.
Current assignment is the K4 kernel repro, superseding the historical projection-formula leaf.
The repro's mathematical inputs already exist; route (B) does not remove its required finite Tate
reading comparison. No heartbeat changes or local Lean/lake executions.

19:45 CST: Shared LEAD diagnosis isolates synHread. Building an independent ordinary pullback
implementation (functors, adjunction, compositors and identities), coefficient vocabulary, finite
module equivalence and reading constructors. Original constructions will appear only in boundary
identifications. All new modules have profiler enabled. First batch tests foundational constructors.

19:48 CST: First ucheck dd5b262f22 is not green: duplicated notation was local to sections,
so declarations after those sections failed parsing. Fixed by keeping the duplicate namespace's
scoped notation. Also corrected a missing X binder in the generated coefficient file. The run
continues rebuilding prerequisite cache; no second build launched. Prepared separate finite
reading constructors and iso-level boundary declarations, all profiled with threshold 0.

19:55 CST: Batch 195111 green for duplicated Pullback, ChangeCoefficients, Coefficient,
Tower, FreeCoefficientPull, FiniteRoots, IntegralPullback, Scalars, TowerProjection,
ChangeCoefficientsComp, IntegralReduction, TowerReduction, PullCoefficientComposition,
TateCoefficientComposition, TowerDoubleReduction. FinitePullback has an ordinary rewrite
failure: old constant-section morphism's codomain leaks original continuousMapRingObj into the
new coeffRing interface. Added a typed coeffSection. IntegralReductionPullback kernel timed out
(60.9s cumulative): its supplied coefficient morphism still inferred the OLD target object.
Now reconstructing finiteReduction/compositeReduction/integersModPowReduction with explicit new
coefficient codomains. This is exactly the implicit-data mixing warned against in strategy 3.

19:56 CST: Breakthrough on the reduction half: IntegralReductionPullback GREEN9.8s in195405
once finiteReduction/compositeReduction explicitly target coeffRing. Previous version had kernel
60.9s timeout. Scalars ordinary rewrite fix prepared; new const section appeared folded in an
internal change command, so keep that proof's raw section expression while its exported statement
uses the typed new section. Next target includes original-statement boundary and axiom print.

20:06 CST: Read refreshed brief and K4-plan-2; now Experiment3 dedicated coefficient category,
minimal interface and one outer interpretation. Snapshot affd8ca0f/log195648 proves the COMPLETE
native finite integral Tate reading square: final kernel707ms, logged elaboration184ms, module8.3s.
Native finite reading kernel63.6ms; actual integral reduction kernel1.19s. All normal/exposed.
The separate FiniteBoundary only fails at upperStarFiniteCoefficientModEquivalenceIso_eq (rfl):
kernel62.2s; other boundaries finiteEquiv293ms, freeRootsIso368ms, readingIso414ms GREEN.
No original final statement has passed. K4C_BENCHMARK.tsv records individual profiler messages
for all current helper declarations (raw elaboration messages do not include tactics/TC synthesis).
Next: keep native proof, inspect minimal dedicated category interface and a single interpretation;
replace the expensive defeq comparison with small propositional adjunction/functor identities.

20:07 CST: Minimal dedicated-category prototype prepared: own Object type, own Category instance,
realize/ofSheaf, native geometric pullback, native finite reading and comparison, concrete Tate
objects/isomorphisms/square. No limits, monoidal or derived instances are needed for this square.
It interprets the already rebuilt native constructions and never invokes the old reading square.
One fully faithful realization is the intended outer operation. Separate generic boundary test
now uses adjunction/low-level iso identities instead of asking rfl to unfold the full mate iso.
