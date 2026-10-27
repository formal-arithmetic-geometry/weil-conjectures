## What changed

Proved `AlgebraicGeometry.isLocallyNoetherian_of_etale_cover` in
`Sheaf.AlgebraicGeometry.EtaleLocalNoetherianDescent`, preserving its statement and
public imports. The proof implements the existing DAG plan entirely from Mathlib.

For every component of the target's affine open cover, pull back the given étale
cover. The projection to an original component is an open immersion, so its
source is locally Noetherian. Étale maps are open, making the pulled-back cover
quasi-compact. `QuasiCompactCover.exists_hom` then gives a finite affine refinement
whose components remain locally Noetherian by their open immersions.

Equip each component's global sections with the algebra structure induced by its
map to the affine base. These algebras are flat and Noetherian. Their finite
product is flat by the direct-sum equivalence and Noetherian by Mathlib's finite
product instance. For a prime of the base, joint surjectivity supplies a point of
a refined component above it; pull its prime back along the product projection.
Naturality of `Scheme.isoSpec` verifies that it lies over the prescribed prime.
`Module.FaithfullyFlat.of_comap_surjective` and
`Submodule.IsNoetherian.of_isNoetherian_tensorProduct_of_faithfullyFlat`, using
the tensor-product right-unit equivalence, descend Noetherianity to the base.
Finally apply open-cover locality.

Added the proof import `Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen` for
openness of the étale maps. No declarations, definitions, or consumers changed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.isLocallyNoetherian_of_etale_cover`
(node `lem-trf-etale-local-noetherian-descent`).

Holes closed: 1. Holes added: 0. Holes remaining: 0. Split-off statements: 0.
Every dependency used is proved in Mathlib; no project theorem with `sorry` is
imported. The cleaned file compiled successfully in 5.4 seconds with no diagnostics.
The delivery also runs the compiler and axiom probes.

## No longer needed

Removed redundant direct proof imports, whose needed declarations remain
available transitively through the retained imports:

- `Mathlib.AlgebraicGeometry.Sites.MorphismProperty`
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`
- `Mathlib.AlgebraicGeometry.Restrict`
- `Mathlib.RingTheory.Flat.Basic`
- `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`

No mathematical DAG dependency is pruned. The proof follows the existing plan;
no Sheaf or WeilConjectures module becomes unnecessary through this delivery.
The open-preimage step is implemented directly by the open-immersion instance
for the pullback projection rather than constructing the open-preimage
isomorphism explicitly.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The original broad proof-import list lacked
`Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen`, needed to name
`Scheme.Hom.isOpenMap` explicitly. No change to the statement or unit route was
needed. Empty targets and empty finite refinements require no separate case:
the finite-product and spectrum arguments already accommodate them.

## Second reading by S8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
