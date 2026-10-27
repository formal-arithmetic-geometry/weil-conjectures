## What changed

Proved `AlgebraicGeometry.VectorBundleZeroSection.finite_type_frames` without changing
its statement, public imports, or the bundle definitions. The proof uses the existing
`trivializationMap_spec`, `transition_spec`, and `zero_spec` directly. Proved private
helpers choose finite affine frame covers, restrict frames with their precise sections,
and establish smoothness and the rank-zero isomorphism. Updated the item's DAG proof
to this route; no other modules are adapted.

The empty base receives an empty cover. The argument never assumes separatedness of
the base or affineness of overlaps. Smoothness is checked locally on the target with
constant relative dimension, so it also gives local finite type.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.VectorBundleZeroSection.finite_type_frames`
(node `lem-pur-vector-bundle-finite-type-frames`). Added zero holes and split off zero
statements. No `sorry` remains in the delivery. All private helpers are proved.

## No longer needed

Removed direct proof imports:
- `Mathlib.LinearAlgebra.SymmetricAlgebra.Basis`;
- `Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties`;
- `Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebraAffine`;
- `WeilConjectures.AlgebraicGeometry.AffineMorphismRelativeSpec`.

The auxiliary `Mathlib.CategoryTheory.Adjunction.Limits` import tried during development
was redundant and is absent from the delivered file. The new proof import
`Mathlib.AlgebraicGeometry.Morphisms.IsIso` supplies target locality of isomorphisms.
The existing proof import of the source smoothness module supplies affine-space
smoothness of relative dimension equal to the number of variables.

Removed these direct DAG proof dependencies:
- `pqf-lem-affine-local-target`: affineness is already part of the constructed `over`;
- `lem-weil-pbc-lft-pointwise-criterion`: smoothness implies local finite type;
- `lem-weil-pbc-smooth-local-on-source`: use target locality of relative-dimension smoothness;
- `lem-weil-pbc-symmetric-algebra-free-module-polynomial`;
- `lem-weil-pbc-quasi-coherent-symmetric-algebra-affine`;
- `lem-weil-pbc-affine-morphism-relative-spec`.

The last three constructions are already encapsulated in `VectorBundleZeroSection`'s
proved chart API and remain necessary there. Thus this delivery withdraws no module
and does not claim those modules leave the targets' import closure. All public imports
and all upstream declarations are preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was wrong. The original plan reconstructed charts already
proved by `trivializationMap_spec`, and reconstructed transition matrices already
proved by `transition_spec`. The Lean proof reuses those results. The rank-zero clause
follows from target locality of isomorphisms and the existing zero-section equation;
it needs no new symmetric-algebra construction. The original existential Noetherian
witness is used through typeclass inference; its unused-variable linter is disabled
only for the unchanged theorem declaration.

## Second reading by P2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
