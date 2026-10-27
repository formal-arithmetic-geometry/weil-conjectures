## What changed

Replaced the proof of `AlgebraicGeometry.exists_intrinsic_resolution_of_embedded` without
changing its statement or any existing definition or public import. The completed assembly
uses three separately stated parts of the reviewed argument.

The affine embedding clause uses the already proved source-library theorem
`exists_isClosedImmersion_affineSpace_of_isAffine`. The ambient is finite-dimensional
relative affine space over the rational field, and its projection has all the required
smoothness, separation and finite-type properties. For the coproduct clause, Mathlib makes
the finite coproduct of the input affine schemes affine. Its colimit isomorphism transfers
this property to the supplied target scheme, to which the affine embedding argument applies.
This proves the empty coproduct case as well, without choosing coproduct ambient embeddings.

For each embeddable input the proof obtains one ordinary tower from its chosen embedded
tower. The proved private helper `change_embedding` constructs its identification with every
other embedding using the supplied intrinsic comparison; it verifies the initial map, labels
and actual center ideals. `change_embedding_cocycle` proves the cocycle using
`E.intrinsicComp` and cancellation of the intermediate embedding isomorphism. The main proof
then chooses a smooth comparison for each smooth rational map, uses the rigidity theorem for
its `unique` field, and uses the chosen comparison's compatibility for its `ambient` field.
All choices of unproved existence witnesses occur inside this existential theorem proof;
there is no definition selecting data from a sorry theorem. The new private data helper
only composes supplied isomorphisms and has no sorry dependency of its own.

The three new modules state individual lower obligations: conversion of one embedded tower,
uniqueness between two fixed ordinary towers, and existence/ambient compatibility of a smooth
comparison between two already supplied towers. None asserts an intrinsic assignment, affine
embeddability, or the change-of-embedding cocycle. Their docstrings and DAG nodes retain the
reviewed geometric proofs and all chart-lifting, ideal-descent and flat-base-change steps.
The item node now records the actual assembly proof and these three dependencies.

Validation: all four delivery modules are checked through the prescribed remote compiler;
final compile and delivery gate results are recorded by the delivery tool. Source checks
also verify line width and the existence of every new node's dependencies.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.exists_intrinsic_resolution_of_embedded`
(node `lem-trf-embedded-to-intrinsic-smooth-resolution`). Its proof, including the two embedding
clauses and transport/cocycle helpers, is complete relative to the three imported statements.

Added exactly three holes, each the entire proof of a public theorem in its own module:

- `AlgebraicGeometry.exists_ordinary_tower_of_embedded`, node
  `lem-trf-embedded-resolution-ordinary-tower`;
- `AlgebraicGeometry.intrinsic_resolution_pullback_subsingleton`, node
  `lem-trf-intrinsic-resolution-pullback-rigidity`;
- `AlgebraicGeometry.exists_intrinsic_smooth_comparison`, node
  `lem-trf-intrinsic-resolution-smooth-comparison`.

The item has zero remaining direct sorries; the delivery has three. This is a decomposition
of one upper hole into three strictly smaller geometric obligations, not a net hole reduction
or an unconditional proof of the resolution theorem. No other existing hole is changed.

## No longer needed

Removed these proof-only imports from the item:

- `WeilConjectures.Compactification.StrictTransformBlowup`;
- `WeilConjectures.Blowup.Principalization`;
- `WeilConjectures.Blowup.BlowupUniversal`;
- `WeilConjectures.Blowup.FlatBaseChange`;
- `Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres`;
- `Mathlib.AlgebraicGeometry.Noetherian`;
- `Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties`;
- `Mathlib.RingTheory.Smooth.StandardSmoothCotangent`;
- `WeilConjectures.RingTheory.StandardSmoothQuotientLift`;
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber`.

Their geometric work is still needed in the new lower obligations; it is not claimed globally
pruned. All twenty former direct proof dependencies are retained below the split, except that
`lem-weil-pbc-lft-affine-pairs` remains direct as well. The affine/disjoint-union clause itself
needs neither standard-smooth quotient lifting nor a disjoint union of ambient schemes: the
proved affine-space closed-chart theorem and finite affineness suffice. No module is withdrawn,
and no node or source-library declaration is removed. No globally pruned module is claimed.

Deleted obsolete direct `tool_uses` approvals from the item node, retaining its existing
`lem-weil-pbc-lft-affine-pairs` entry in order. These tools still appear where their geometric
steps occur in the new nodes; no new maintainer approval is invented.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed or disputed. The source library already proves the
affine closed-embedding result, and Mathlib's finite affine coproduct instance shortens the
second clause. The reviewed plan did not need to construct separate disjoint ambient unions.

The original strict-transform dependency's recorded primary declaration is the closed
immersion result, whereas the conversion requires the stronger
`exists_blowup_comap_iso_strictTransform`, already proved in that same module. The new
conversion node names the exact usable declaration rather than treating existence of a closed
immersion alone as an identification with the ordinary blowup.

The uniqueness part is isolated explicitly: smoothness of the next cartesian projection
makes pullback of the invertible exceptional ideal invertible, allowing the blowup universal
property to compare maps over the preceding level. The rigidity statement does not assert
uniqueness of arbitrary maps into a blowup without this invertibility condition.

The new comparison node retains uses of generic tools from other units already approved for
the parent plan (strict transforms, standard-smooth chart lifting, and flat blowup base
change). These are the same generic-tool uses moved to the appropriate lower obligations;
if tool-use approvals must be attached to each new node, the maintainer should transfer those
approvals at review. The unit's own realization and route are unchanged.

## New nodes

`lem-trf-embedded-resolution-ordinary-tower` in
`Sheaf.AlgebraicGeometry.EmbeddedResolutionOrdinaryTower` makes Step 1's conversion of one
specified embedded tower into an ordinary tower precise. Its proof enumerates finite labels,
uses the strict-transform/blowup isomorphism, and transfers the center and regularity fields.
This obligation contains no smooth comparison or assignment on multiple inputs.

`lem-trf-intrinsic-resolution-pullback-rigidity` in
`Sheaf.AlgebraicGeometry.IntrinsicResolutionPullbackRigidity` states uniqueness for two fixed
ordinary towers over a fixed smooth morphism. Its proof is finite induction using
principalization, flatness and the uniqueness part of the blowup universal property. It
constructs neither a tower nor a comparison.

`lem-trf-intrinsic-resolution-smooth-comparison` in
`Sheaf.AlgebraicGeometry.IntrinsicResolutionSmoothComparison` treats two fixed towers already
identified with the embedded assignment. It records the standard-smooth chart lifting,
open restrictions, ideal descent, flat blowup induction and compatibility with supplied
cartesian embedded comparisons of Steps 3--9. It constructs no global intrinsic assignment
and does not assume the desired comparison as a hypothesis.

All three inherit the item's chapter, unit and blueprint ancestry; each has recorded actual
Mathlib searches. No change record is needed: only this item's proof/node and new modules/nodes
are changed, with all existing signatures, public imports and definitions preserved.

## Second reading by W4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
