## What changed

Implemented the finite-affine-atlas refinement after its finite image selection step.
The proof constructs the actual scheme coproduct and its map to the specified atlas,
lifts its coprojections to Over S, and proves the commuting triangles. Etaleness follows
from source locality for the coproduct map, scheme pullback base change, and the existing
proved representable-etale composition theorem. A proved private helper establishes
scheme-test surjectivity directly from the field-extension joint-surjectivity condition,
using the existing proved scheme-fibre-product point theorem. The product-of-rings
spectrum formula uses coproduct reindexing through ULift to handle arbitrary universe u.
The empty coproduct is identified with Spec PUnit through its initial universal property.
The affine-atlas corollary now follows from the refinement.

Added AlgebraicSpaceFiniteAffineImageSelection, isolating only the finite affine image
subcover (original Steps 1-2). It asserts neither a coproduct nor an affine atlas nor any
spectrum formula. Its source and complete proof in words are in its docstring and node.
This is a reduction of the original argument, with all remaining assembly written in Lean.
Existing public imports, signatures and docstrings are preserved. No existing module
other than the assigned item changes.

Validation: lcompile.py --all compiled both delivered modules with no errors or warnings
(selection 3.8 s, item 20.3 s). Both existing signatures and all existing public imports
were compared verbatim. The updated dependency closure has no cycles or missing nodes.

## Proved and sorry left

Original holes replaced by complete Lean proof terms:

- AlgebraicGeometry.AlgebraicSpace.exists_finite_affine_atlas_refinement, node
  lem-trf-space-qc-finite-affine-atlas-refinement: reduced to the finite image selection
  below, with the coproduct, representable-etale, surjectivity, spectrum and empty-case
  assembly proved.
- AlgebraicGeometry.AlgebraicSpace.exists_affine_atlas_of_quasiCompact, same node:
  proved from the preceding refinement.

One hole added, and the only sorry in this delivery:

- AlgebraicGeometry.AlgebraicSpace.exists_finite_affine_image_selection, node
  lem-trf-space-finite-affine-image-selection.

There are zero textual holes left in the item, one in the new module: two original
holes closed, one strictly smaller step split off. The main theorem is a decomposition,
not a claim that finite image selection has been proved. Neither private helper has a hole.

## No longer needed

Removed proof imports from the assigned item:

- Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
- Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus
- Mathlib.Topology.Compactness.Compact
- Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

The first three belong to the remaining finite image selection argument; they have not
been declared mathematically unnecessary. Pullback infrastructure remains available from
public imports and is used by the proved scheme-test helper. The original point-calculus
tool approval is removed from the parent's direct tool_uses; the new selection node
records why that same generic tool is needed for its proof. No module is withdrawn.
No original mathematical dependency is pruned from the entire argument: the compactness
and point-image dependencies move to the selection node, and the coproduct, base-change,
etale-locality and finite-spectrum dependencies remain used in the parent.

The parent's proof now uses the already proved lem-a1-space-fibre-product-point directly
for surjectivity, rather than applying the point-map criterion of
lem-a1-space-point-open-calculus in that step. The latter is still needed for selection.

## Where the brief, the DAG or earlier work was wrong

No statement correction. The point-open-calculus theorem's formal surjectivity criterion
is for morphisms between algebraic spaces, whereas the atlas in the item is a map from a
Yoneda scheme presheaf. The field-extension covering condition and the existing
scheme-fibre-product point theorem give a direct scheme-source argument, avoiding an
additional bridge or a second sorry. Mathlib sigmaSpec indexes schemes and rings in the
same universe; the Fin n version of the formula needs the proved ULift reindexing and
product-ring isomorphism. The empty case uses the empty-diagram colimit equivalence.

The new selection statement was checked for empty target/atlas, n=0, arbitrary noncompact
W, overlapping affine opens, and no separatedness assumption. These agree with Stacks
03E4/03H6. The unit and chapter route are unchanged.

## New nodes

lem-trf-space-finite-affine-image-selection is the original compactness and finite-subcover
portion, with an explicit empty-atlas choice. It is strictly smaller than the parent and
has a new module with one named public sorry theorem. Searches by LeanSearch, LeanFinder,
Loogle, Mathlib grep, local source grep and blueprint search found scheme compactness tools
and the disjoint-component finite-subatlas theorem, but no duplicate of this statement.
There is no interface change and hence no change record or consumer adaptation.

## Second reading by U1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
