## What changed

Proved `AlgebraicGeometry.composite_fibre_local_models` in
`lean/Sheaf/AlgebraicGeometry/CompositeFibreLocalModels.lean`. Added the proved dependency
module `lean/Sheaf/AlgebraicGeometry/FibreStalkQuotient.lean`, defining the canonical fibre
stalk map and proving its surjectivity, kernel, and quotient equivalence. The main proof uses
Mathlib's locally finite type Noetherian fibre results, pullback lifts, an explicit quotient
argument, pushout stability of flatness, and residue-field functoriality. The interface/import change is recorded in
`coord/changes/composite-fibre-local-models-imports.md`.

## Proved and sorry left

Closed the `sorry` in `AlgebraicGeometry.composite_fibre_local_models` and the `sorry` in
`AlgebraicGeometry.Scheme.Hom.fiberStalkMap_surjective_ker_quotientEquiv`. No `sorry` remains
in either delivered module.

## No longer needed

Removed the proof-only imports of `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
`Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`,
`Mathlib.AlgebraicGeometry.Morphisms.Immersion`, `Mathlib.AlgebraicGeometry.Morphisms.Separated`,
`Mathlib.RingTheory.FiniteType`, `Mathlib.RingTheory.Localization.Submodule`,
`Mathlib.RingTheory.Flat.Stability`, `Mathlib.LinearAlgebra.TensorProduct.Quotient`, and the
unused public import `Sheaf.Topology.PresheafModuleStalkFunctor`. The proof does not need the
DAG nodes for proper finite-presentation permanence, affine-pair finite type calculations,
finite-type algebra Noetherianity, affine-stalk localization, localization Noetherianity, or
flat module quotient flatness; Mathlib's fibre and Noetherian APIs supply the used results.

## Where the brief, the DAG or earlier work was wrong

The planned proof's long affine chart calculation is unnecessary in the available Mathlib API.
The missing implementation of `lem-sbc-scheme-fibre-stalk-quotient` was the only substantial
bridge; it is now proved directly from the fibre pullback and the first isomorphism theorem.

## New nodes

None. The delivery implements the existing dependency node
`lem-sbc-scheme-fibre-stalk-quotient` and updates the item's proof route.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
