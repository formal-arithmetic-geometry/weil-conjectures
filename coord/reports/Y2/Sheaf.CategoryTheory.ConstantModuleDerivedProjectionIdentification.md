## What changed

Completed the body of
`CategoryTheory.ConstantModuleDerivedProjection.etale_constant_module_derived_projection_identification`
without changing its statement, any existing definition, or the general comparison theorem.
The proof retains the canonical ordinary etale tensor structure, reuses the existing
exactness, derived scalar-comparison and bounded-below constructors, and constructs
`EtaleIdentification` with exactly its prescribed left and right isomorphisms.

The new proved private helper `etaleAdjunctionSquare` derives the full Hom square from
`AlgebraicGeometry.Etale.mapDerivedUpperStarLowerStarAdjunction_eq`, the transport formula
for `Adjunction.ofNatIsoLeft`, and the identity derived natural-isomorphism formulas.
The existing abstract projection-mate theorem then gives the projection square from
the tensor and adjunction squares. Neither square is an added assumption or hole.

Three proof-only imports were added: the two new statement modules below, and
`WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarAdjunctionCompat`.
The item node's last proof step and proof dependencies now describe this assembly.
Existing public imports and declaration signatures remain unchanged.

## Proved and sorry left

One of the item's one original holes is closed by decomposition:
`CategoryTheory.ConstantModuleDerivedProjection.etale_constant_module_derived_projection_identification`
(node `lem-sfb-constant-module-derived-projection-identification`). No sorry remains in
the item module. Its general comparison theorem was already proved and is unchanged.

Two holes are added, each in a new public theorem and its own module:

- `CategoryTheory.ConstantModuleDerivedProjection.etale_constant_module_geometric_realization`
  (`lem-sfb-etale-constant-module-geometric-realization`): ordinary geometric realization,
  equality with the published ordinary adjunction, and canonical ordinary tensor data.
- `CategoryTheory.ConstantModuleDerivedProjection.etale_constant_module_tensor_normalization`
  (`lem-sfb-etale-constant-module-tensor-normalization`): equality of normalized derived
  tensorators under the specified exact/left-derived comparison.

This is a decomposition, not a net hole reduction: one upper hole closed, two lower
holes added. The first statement involves no derived categories; the second involves
no derived adjunction, projection square, bounded-below comparison or scalar-derived
identification. The Lean proof combining them is complete. Both statements include
source citations, full proof plans and matching DAG nodes. No data definition uses sorry.

## No longer needed

No existing import, module, node or top-level tool approval is removed. The earlier
etale proof step's inverse-image and tensor dependencies remain needed through the two
new statements, so they are not claimed as pruning. No source-library declaration is
removed or changed, and the unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

No original statement is disputed. The old final proof step suppressed two substantial
normalization bridges: constructing the entire ordinary geometric datum with the
published module adjunction, and comparing the normalized exact derived tensorator
with the K-flat etale tensorator. Those are the two remaining statements above.
The ordinary monoidal structure is explicitly identified in the first bridge and is
an explicit hypothesis in the second; equality of inverse-image functors alone would
not specify a tensorator normalization.

Existing exact/K-flat derived-adjunction comparison supplies the adjunction bridge,
so no new adjunction or projection-formula lemma is needed. The tensor uniqueness
argument uses the scalar tensor equivalence and ringed resolving localization only
as generic tools; it does not replace a step of proper base change. The geometric
bridge similarly uses ordinary module inverse image and its canonical tensor map.

## New nodes

`lem-sfb-etale-constant-module-geometric-realization`, in
`Sheaf.CategoryTheory.EtaleConstantModuleGeometricRealization`, records the ordinary
realization and canonical ordinary monoidal normalization. Source: Modules on Sites,
Tags 03D6 (`definition-pushforward`), 03D7
(`lemma-adjoint-pullback-pushforward-modules`) and 03EL
(`lemma-tensor-product-pullback`). Its proof uses the existing exact etale module
inverse-image construction and ordinary ringed tensor construction. The monoidal
etale API is a generic tool from `lem-kun-inverse-image-monoidal`.

`lem-sfb-etale-constant-module-tensor-normalization`, in
`Sheaf.CategoryTheory.EtaleConstantModuleTensorNormalization`, records only the tensor
square. Source: Cohomology on Sites, Tag 07A4 (`lemma-pullback-tensor-product`). Its
proof computes on flat-term K-flat complexes and descends using the existing
constant-scalar tensor equivalence and site-derived tensor descent. These are generic
tools, not alternate proper base-change routes. Both new nodes inherit the item's
blueprint ancestor and cite its projection-map identification step. LeanSearch,
Loogle/LeanFinder and Mathlib-source searches found no exact existing statement.

There are no change records because no existing statement or definition was changed.

## Second reading by Y2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
