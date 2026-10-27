## What changed

Reduced `bundleOrientation_purity` to the canonical projection identity at the coefficient
unit. The item proves the remaining cancellation, adjunction transport, and tensor-unit
naturality by a private categorical lemma `normalized_adjunct`. The new proof-only import
is `Sheaf.AlgebraicGeometry.BundleSectionProjectionUnit`; the generic categorical proof also
imports `Mathlib.CategoryTheory.Monoidal.CoherenceLemmas`. Existing signatures and definitions
are preserved.

## Proved and sorry left

Closed the item's hole `AlgebraicGeometry.Etale.FiniteRingSectionDeformation.bundleOrientation_purity`
by decomposition, adding one strictly simpler hole
`AlgebraicGeometry.Etale.bundleSectionProjection_unit`
(node `lem-trf-bundle-section-projection-unit`). This is a decomposition, not a net hole reduction.

The two untouched item holes are
`AlgebraicGeometry.Etale.FiniteRingSectionDeformation.coordinate_normalization` and
`AlgebraicGeometry.Etale.FiniteRingSectionDeformation.bundleOrientation_frames`, both attached
to `lem-trf-finite-ring-section-deformation`. The delivery contains three holes in total:
two in the item and one in the new module.

## No longer needed

None. The earlier coordinate, frame, and geometry dependencies remain needed. No source
module, public declaration, or unit route is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The previous attempt's no-space failure is no longer occurring. The projection-unit identity
is needed as a separate coherence step: it has no trace or exceptional adjoint, whereas the
item compares the integration adjunct and the inverse-projection purity adjunct. The
remaining categorical assembly is proved in Lean. Profiling also exposed expensive unfolding
of the concrete frame coordinate map; local irreducibility prevents that unfolding without
changing any construction or exported attribute. The coefficient object is likewise sealed
locally, and the monoidal instances are aligned with the defining derived-tensor modules.
The compact-support alias is locally semireducible where the generic adjunction proof
needs its functor identity. The file uses synchronous elaboration. A full `lcompile.py --all`
compile of the reduction passed; profiling commands were then removed for delivery.

## New nodes

`lem-trf-bundle-section-projection-unit` records precisely the coefficient-unit projection
coherence identity, in `Sheaf.AlgebraicGeometry.BundleSectionProjectionUnit`. The statement
has no integration trace, inverse projection, or exceptional adjunction. Its docstring gives
the full proof by pullback-unit coherence, braiding naturality, and projection right unitality.
The edge cases rank zero, empty base, and zero coefficient ring use the same unit equations.

## Second reading by M7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
