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
