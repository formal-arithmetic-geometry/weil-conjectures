## What changed

Filled the two proofs in `Sheaf.Paper.EtaleDirectImageScalarComposition`, retaining
both public signatures and all original public imports. Composition uses the existing
composite and iterated adjunct lemmas, with an explicit transport between total left
derived pullback and exact levelwise pullback. Identity uses the existing scalar/pullback
identity normalization and the ordinary identity counit, transported through the canonical
derived-functor comparisons. Three proved private helpers supply the categorical transport
and identity comparison calculations. No definition or statement was changed.

Added private proof imports of `Sheaf.Paper.ScalarCompositeMateAdjunct`,
`Sheaf.Paper.ScalarIteratedMatesAdjunct`,
`Sheaf.Paper.EtaleScalarPullbackIdentityNormalization`,
`WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarAdjunctionCompat`, and
`WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionIdIso`.
Updated the existing node's proof, proof dependencies, proof origin and obsolete tool uses
to describe this assembly. The blueprint unit route is preserved.

## Proved and sorry left

Closed the two existing holes:

- `AlgebraicGeometry.Etale.scalarMate_directImage_composition`.
- `AlgebraicGeometry.Etale.scalarMate_directImage_identity`.

Item holes remaining: 0. Holes added: 0. Statements split off: 0.
The complete item compiled cleanly through `lcompile.py` in 23.2 seconds.
The existing identity-normalization dependency is used as stated; its proof is outside
this packet. No new public declarations or modules are introduced.

## No longer needed

Removed the original direct private imports:

- `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`.
- `Sheaf.Paper.ScalarPullbackComposition`.
- `Mathlib.CategoryTheory.Adjunction.Basic` (already available through statement imports).
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.

Removed `lem-sfb-ringed-derived-monoidal-comparisons` from this node's direct proof
dependencies: the composite adjunct lemma already supplies the composition calculation,
and the concrete identity counit is proved locally. Removed the obsolete top-level tool-use
entries `lem-sfb-ringed-derived-monoidal-comparisons`,
`lem-sf-scalar-pullback-composition`, and `lem-pc-kflat-resolution`.
These results can remain transitive dependencies of the existing imported lemmas;
this packet does not withdraw any module or claim that they are globally unreachable.
The existing public imports remain part of the module's exported interface.

## Where the brief, the DAG or earlier work was wrong

The two adjunct statements use different models of exact inverse image. Their
comparison requires transport through `leftDerivedUpperStarIsoMapDerivedCategory`;
they cannot be equated literally. The proof supplies that transport by naturality
and inverse cancellation. The generic ringed comparison system alone does not identify
the concrete small-etale identity maps appearing in this signature; the proof instead
uses the ordinary identity counit and canonical derived-functor comparisons.

## Second reading by W7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
