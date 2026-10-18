## What changed

Proved `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_of_coherent_free_stalks`.
The proof uses the existing coherence-to-quasi-coherence/finite-type theorem, the affine
finite-locally-free criterion, and the affine germ localization theorem. A private helper
proves flatness of sections by checking localized maximal ideals: the localized section module
is free by base change from the given finite-free stalk, and hence is flat.

The proof-only imports now include the source modules providing affine germ localization and
the affine finite-locally-free criterion. Three unused Sheaf proof imports were removed.
The copied DAG node records the shorter route and its four actual proof dependencies.

## Proved and sorry left

Closed the one sorry in
`AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_of_coherent_free_stalks`.
No sorry remains in the assigned module, and no new sorry or intermediate node was added.

## No longer needed

Removed these unused imports:

- `Sheaf.AlgebraicGeometry.AffineFiniteModuleFreeLocus`
- `Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`
- `Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine`

The original blueprint proof dependencies `pqf-def-locnoeth`,
`lem-weil-pbc-affine-tilde-gamma-adjunction`,
`lem-weil-pbc-spec-tilde-stalk-localization`, and
`lem-sc-affine-finite-module-free-locus` are not used. The affine criterion and the existing
`lem-sbc-affine-module-germ-localization` theorem subsume those steps directly.

## Where the brief, the DAG or earlier work was wrong

The blueprint route expands an affine sheaf into a tilde module and then invokes a free-locus
cover. The published library already has a criterion stated directly for every affine open and
an existing localization theorem for the section-to-stalk germ. Following those declarations
makes the expansion and free-locus-cover steps redundant; no target statement was changed.

## New nodes

None.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
