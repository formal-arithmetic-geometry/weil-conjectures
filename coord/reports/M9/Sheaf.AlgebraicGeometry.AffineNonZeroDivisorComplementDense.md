## What changed

Proved `AlgebraicGeometry.PrimeSpectrum.basicOpen_app_injective_and_dense_of_nonZeroDivisor`
without changing its statement. Replaced the two private proof imports by
`Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant`.
The localization map is injective; the global-sections isomorphisms transfer
this to the induced map of spectra. Its kernel ideal sheaf is zero because the
target is affine. Transporting along `basicOpenIsoSpecAway` makes the principal
open inclusion scheme-theoretically dominant, giving injectivity on every open
and topological density. Updated the existing node's proof and dependencies.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.PrimeSpectrum.basicOpen_app_injective_and_dense_of_nonZeroDivisor`
(node `lem-pc-affine-nonzerodivisor-complement-dense`).
Holes closed: 1. Holes added: 0. Sorry left in the delivery: none.

## No longer needed

Removed private imports `Sheaf.AlgebraicGeometry.PrincipalOpenDenseOfNonZeroDivisor`
and `WeilConjectures.Blowup.BlowupUniversal`.
This proof no longer needs `lem-pc-principal-open-dense-of-nonzerodivisor`
or `lem-pc-localization-preserves-nonzerodivisor`: the global affine kernel
calculation gives both conclusions directly. The remaining declared dependency
is the Mathlib leaf `lem-pc-affine-localization-injective` (`IsLocalization.injective`).
No declarations or modules are withdrawn; the removed dependencies can still
have other consumers. The unit's statement and realized steps are preserved.

## Where the brief, the DAG or earlier work was wrong

The planned basis calculation and the separate minimal-prime argument are
unnecessary for this item. Mathlib already transfers injectivity on global
sections of an affine target to the required conclusion through the kernel
ideal sheaf. The source statement and all hypotheses remain unchanged,
including for the zero ring and for a unit as generator.

## Second reading by M9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
