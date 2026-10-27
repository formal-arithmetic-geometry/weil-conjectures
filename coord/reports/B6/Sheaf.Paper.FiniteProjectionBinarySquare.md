## What changed

The existing statement `exists_component_binary_square` is unchanged. Its proof
constructs the compatible Cartesian triangle over the prescribed compactification,
uses `compositionProjectionMate`, and pastes the realized square by cancelling
explicit endpoint isomorphisms through the faithful constructible inclusion.
The raw factor-projection calculation and cancellation are proved locally. The new
comparison maps use the raw tensor bifunctor at their boundaries, matching the
existing triangle law directly.

Two new modules separate the coefficient-coordinate calculations: iteration of two
projection components, and the projection-free normalization of the two compositor
endpoints. Their comparison objects are explicit composites of existing units and
support/pullback comparisons. Generic category constructions give both target isomorphisms, together with proved
forward-map formulas that avoid unfolding concrete derived resolutions.
The triangle arrow's inverse is uniquely determined by its isomorphism property.
No object is chosen from an unproved mere-existence theorem.
`fixedScalarTensorData` retains the published `fixedTensor` name in the raw
bifunctor. Its equality to `ordinaryTensor`, including both projection fields, is
proved by `fixedScalarTensorData_eq` using `rfl`.
The endpoint equations are packaged in a proof-only proposition structure. Its source
field uses the forward native compositor, so the pasting argument cancels only the
target comparison. Local reducibility attributes keep the derived tensor and derived
functors folded during elaboration; no shared attributes changed. A local proposition
wrapper isolates the change of morphism indices from the derived-morphism proof,
and generic proved transport lemmas handle the positive coefficient exponent and
the tensor-data equality.
Only proof imports were added to the existing module. No shared definition, existing
statement, target, source-library declaration or public import changed.

## Proved and sorry left

The original hole `exists_component_binary_square` is closed by a complete proof
from the declared dependencies and the new normalization theorem. The additional
`iteration_realization` theorem is proved completely, including support naturality,
projection naturality and coefficient-unit cancellation.

Three holes are added:
`binary_iteration_triangle_pasting` (node
`lem-sf-finite-projection-binary-iteration-triangle-pasting`),
`binary_composition_realization` (node
`lem-sf-finite-projection-composition-realization`), and
`binary_square_on_triangle` (node
`lem-sf-finite-projection-binary-triangle-square`). Each proof is exactly
`:= by sorry`. There are zero holes in the original item and zero in
`FiniteProjectionIterationRealization`. Thus one original hole is closed and three
strictly simpler holes are split off; this is a decomposition, with no net hole
reduction claimed.

## No longer needed

No original public import was removed. No existing module is withdrawn.
The item no longer needs a separate invocation of
`lem-sfb-ringed-projection-tensor-composition`: the published proper/open
`compositionProjectionMate` supplies the raw square directly. The Cartesian
compositor and finite-ring origin dependencies are retained as dependencies of
`binary_composition_realization`, rather than asserted pruned. The operation-stage
definition remains needed by all statements. No global pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The original plan combines two different coordinate calculations in its final
sentence. The new nodes expose their exact equations: iteration transport has no
support compositor, while compositor normalization contains no projection morphism.
The geometric existence, raw triangle projection law and the final cancellation are
not postponed. The unit route and original statement are preserved.

## New nodes

`lem-sf-finite-projection-iteration-realization`, in
`Sheaf.Paper.FiniteProjectionIterationRealization`, records coefficient realization
of two successive projection maps with their explicit endpoints. This theorem is
fully proved using naturality of the two fixed-coordinate components and of the
published support comparison, followed by coefficient-unit cancellation.

`lem-sf-finite-projection-binary-triangle-square`, in
`Sheaf.Paper.FiniteProjectionBinaryTriangleSquare`, records the fixed Cartesian
triangle square with all geometric maps supplied. Its proof is split off as a
strictly simpler intermediate statement.

`lem-sf-finite-projection-binary-iteration-triangle-pasting`, in
`Sheaf.Paper.FiniteProjectionBinaryIterationTrianglePasting`, records the first
projection-free triangle pasting split as a separate statement.

`lem-sf-finite-projection-composition-realization`, in
`Sheaf.Paper.FiniteProjectionCompositionRealization`, records the source and target
normalizations of the support compositor on a supplied Cartesian triangle. Its
statement concerns support, pullback and tensor comparisons, with no projection
component. The proof in words reduces it to the existing finite normalization and
Cartesian-origin compositor declarations. Zero objects, identity maps and empty
schemes introduce no extra assumptions in either equation.

No change records are needed: all additional declarations and data occur in new
modules, and the original item receives a proof and private helpers only.

## Second reading by B6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
