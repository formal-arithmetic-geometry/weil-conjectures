## What changed

Proved `AlgebraicGeometry.ProEtale.QuotientChange.canonicalCoefficientTensorNormalization_normalized`
in `Sheaf.Paper.CanonicalCoefficientTensorNormalization`, keeping its statement and the canonical
normalization definition unchanged. Private helpers make explicit the quotient/single tensor
comparison, compatibility with braiding, the balanced counit, and the exact restriction factor.
The second assertion compares ordinary monoidal unit formulas and then uses the existing exact
single-object comparison. Added a proof-only import of
`WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor`.

Updated the item's DAG proof text to match these calculations. Its dependencies and the unit route
are unchanged. No source-library module, statement, or definition was modified.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.ProEtale.QuotientChange.canonicalCoefficientTensorNormalization_normalized`
(node `lem-sfb-canonical-coefficient-tensor-normalization`). Holes closed: 1; added: 0;
split off: 0; remaining in the item module: 0. Every private helper has a complete proof.

## No longer needed

No imports, nodes, or modules pruned. All four declared proof dependencies remain used. The
ordinary-unit comparison needs only the defining transported monoidal formulas and functoriality;
the planned additional coprojection argument is unnecessary.

## Where the brief, the DAG or earlier work was wrong

The DAG's second step overstates the required unit-map calculation. After exposing the standard
composite monoidal structure, its extra factor is scalar extension applied to the identity unit
morphism of `mapMod`. Removing that mapped identity leaves the transported residue formula
by definitional equality. No change of definitions or statements is needed.

The search for a shorter proof used LeanFinder (derived tensor/counit compatibility), Loogle
(`CategoryTheory.Functor.map_comp`), the logged grep search, and local searches of Mathlib and both
library roots. The existing normalized tensor-presentation theorem supplies the substantive
universal-property step; its remaining cochain and exact-functor equations are proved here.

## Second reading by V4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
