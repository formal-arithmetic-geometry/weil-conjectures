## What changed

Proved `AlgebraicGeometry.ringKrullDim_stalk_lt_top_of_finiteType` in
`Sheaf.AlgebraicGeometry.FiniteTypeLocalDimension`, with its signature unchanged.
The proof establishes `IsLocallyNoetherian X` using
`LocallyOfFiniteType.isLocallyNoetherian` and then applies `ringKrullDim_lt_top`.
Mathlib supplies the Noetherian stalk and finite-dimensional Noetherian local ring
instances. The single-file server compile passed without errors or warnings.
Updated the theorem docstring and its existing DAG node to describe this proof.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.ringKrullDim_stalk_lt_top_of_finiteType`
(node `lem-kun-finite-type-local-dimension`).
Added 0 holes; split off 0 statements. No sorry remains in the delivered module.
The proof uses Mathlib only and introduces no new declarations or definitions.

## No longer needed

Removed redundant private imports `Mathlib.AlgebraicGeometry.AffineScheme`,
`Mathlib.RingTheory.Noetherian.Defs`, and `Mathlib.RingTheory.Localization.Submodule`;
they are already available through the retained imports. No public import changed.

The global Noetherianity/compactness portion of the old argument is unnecessary:
the locally Noetherian clause of `lem-weil-pbc-finite-type-over-noetherian` suffices.
The existing quasi-compactness hypothesis remains in the signature unchanged.
All nine existing proof-dependency nodes remain used, directly or through the
Mathlib instances realizing the affine localization and height-theorem steps.
No DAG node or library module is withdrawn or made unnecessary by this delivery.
The unit record has no realized statement or proof steps to bypass.

## Where the brief, the DAG or earlier work was wrong

The earlier plan is mathematically correct but proves the stronger intermediate
assertion that X is globally Noetherian. The local assertion suffices and is
already a Mathlib theorem. Mathlib also already packages the affine localization
argument as its Noetherian-stalk instance, so no new intermediate lemma is needed.
The empty scheme case is vacuous because the theorem takes x : X; any actual
stalk is a nontrivial local ring, as required by the finite-dimension instance.

## Second reading by T8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
