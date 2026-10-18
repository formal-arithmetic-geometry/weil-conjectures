## What changed

Replaced the sole `sorry` in
`CategoryTheory.Functor.preservesTotalTensorKFlatQuasiIso_of_exact` with a proof
that constructs the preservation class and applies
`HomologicalComplex.quasiIso_map_of_preservesHomology` to its morphism.
Mathlib infers `F.PreservesHomology` using
`CategoryTheory.Functor.preservesHomologyOfExact` from the existing finite-limit
and finite-colimit hypotheses. The two K-flat hypotheses are unnecessary for
this stronger exact-functor preservation result.

The declaration signatures, definitions, visibility, and imports are unchanged.
The existing DAG proof is retained: Mathlib packages exactly its natural
cohomology-comparison and preservation-of-inverses argument. No new proof route,
node, dependency, or statement repair is needed.

LeanFinder and Loogle both returned the applied quasi-isomorphism theorem;
the launcher grep search returned it and the exactness-to-homology instance.
Their pinned Mathlib source signatures and implementations were read, along
with every dependency node and the parent unit. The source references are
Stacks `homology.tex`, lemma-exact-functor (010N), and `derived.tex`,
lemma-right-derived-exact-functor (015F).

## Proved and sorry left

Closed 1 of 1 holes:
`CategoryTheory.Functor.preservesTotalTensorKFlatQuasiIso_of_exact`
(node `def-sfb-preserves-kflat-quasi-iso`).

No holes remain in the item. No holes added and none split off.
Server compilation completed cleanly in 2.4 seconds. A further compilation
with `#print axioms` reported exactly `propext`, `Classical.choice`, and
`Quot.sound`; the diagnostic command was then removed.

## No longer needed

None. No imports removed and no nodes or modules pruned. The cohomology
comparison dependency `lem-weil-pbc-exact-functor-complex-cohomology` is used
through Mathlib's already-proved preservation theorem and exactness instance;
it is not bypassed. The other dependencies provide the unchanged definitions.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface defect found. The DAG already records the
Mathlib preservation theorem in its searches, so its planned argument needs
only a class constructor followed by that theorem. This also covers unbounded
complexes without imposing a tensor structure on the target category or
coproduct-preservation hypotheses on the functor.

## Second reading by V3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
