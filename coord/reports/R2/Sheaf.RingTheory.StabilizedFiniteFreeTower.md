## What changed

Completed the listed retirement of `Sheaf.RingTheory.StabilizedFiniteFreeTower`.
Its only declaration, `DerivedCategory.exists_model_of_stabilized_finite_free_tower`,
duplicates the adopted source theorem
`CochainComplex.exists_model_of_stabilized_finite_free_tower` in
`WeilConjectures.RingTheory.StabilizedFiniteFreeTower`.
The signatures and proof bodies are identical after the namespace rename.

Withdrew the Sheaf file through `deleted.txt`; the delivery tool replaces it with
an empty module. Reattached node `lem-sc-stabilized-finite-free-tower` to the
unchanged source theorem. No source-library module or public import is changed.
The proof, source, statement, proof dependencies and unit route remain the same.
Change record: `coord/changes/retire-stabilized-finite-free-tower.md`.

Checked all Lean sources under both library roots: there are no importers of the
Sheaf module and no qualified uses of its old declaration. The historical consumer
`Sheaf.RingTheory.FiniteLocalizationFreeModel` is already absent. The current
consumer `WeilConjectures.RingTheory.FiniteLocalizationFreeModel` already imports
and applies the source theorem, and needs no adaptation.

Validation used only `lcompile.py`: the original Sheaf file compiled; an example
with its exact statement was proved by applying the source theorem; and the
unchanged source consumer compiled. `#print axioms` on the source theorem reports
only `propext`, `Classical.choice`, and `Quot.sound`. Search via `msearch.py`
(LeanFinder, Loogle, grep) confirmed the Mathlib eventual-constancy infrastructure;
the exact replacement is the existing source theorem.

## Proved and sorry left

This is a retirement with zero original holes, not a new proof or decomposition.
Holes closed: 0. Holes added: 0. Holes left: 0. Split off: 0.

The retired declaration
`DerivedCategory.exists_model_of_stabilized_finite_free_tower` had no sorry.
The retained `CochainComplex.exists_model_of_stabilized_finite_free_tower`
(node `lem-sc-stabilized-finite-free-tower`) has no sorry and only the three
allowed axioms. No other declaration is changed or introduced.

## No longer needed

Pruned module `Sheaf.RingTheory.StabilizedFiniteFreeTower` and its unused duplicate
`DerivedCategory.exists_model_of_stabilized_finite_free_tower`.
Its public imports of `Mathlib.Algebra.Homology.Embedding.CochainComplex`,
`Mathlib.Algebra.Category.ModuleCat.ChangeOfRings`,
`Mathlib.Algebra.Category.ModuleCat.Free`, and
`Mathlib.RingTheory.Localization.Away.Basic`, and its private imports of
`Mathlib.Algebra.Homology.HomologicalComplexLimitsEventuallyConstant` and
`Mathlib.CategoryTheory.Functor.OfSequence`, disappear with the withdrawn module.
These Mathlib modules themselves remain needed by the retained source theorem.

No DAG node is pruned. Node `lem-sc-stabilized-finite-free-tower` remains attached
to the adopted source theorem, with unchanged mathematical statement and proof.
No dependency nodes, source declarations or additional modules are withdrawn.

## Where the brief, the DAG or earlier work was wrong

The generic stage-3 brief describes a proof obligation, but the current queue and
`coord/retire-items.tsv` classify this item as `retire`, with zero holes.
The DAG still named the unused Sheaf copy, even though the adopted source tree
already contains the same theorem in namespace `CochainComplex` and its consumer
already uses that version. This delivery repairs that stale attachment and removes
the duplicate. The retirement inventory's historical Sheaf consumer has already
been retired; the current Lean source scan is authoritative for adaptations.

## Second reading by R2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
