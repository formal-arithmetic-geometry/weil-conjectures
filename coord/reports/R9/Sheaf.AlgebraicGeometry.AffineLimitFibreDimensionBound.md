## What changed

The item module now proves `AlgebraicGeometry.exists_stage_fibre_dimension_le` by classical
contradiction and push-negation, applying the new bad-locus intermediate theorem. The long
bad-locus construction is isolated in the new module
`Sheaf.AlgebraicGeometry.AffineLimitFibreDimensionBoundCore` as
`AlgebraicGeometry.fibre_dimension_contradiction_of_all_stages_bad`, with its proof left for a
follow-up worker. The item imports were pruned to the statement imports and the core proof import.

## Proved and sorry left

The final implication `AlgebraicGeometry.exists_stage_fibre_dimension_le` is proved completely.
One new sorry remains in `AlgebraicGeometry.fibre_dimension_contradiction_of_all_stages_bad`, node
`lem-weil-pbc-affine-limit-fibre-dimension-bound-core`. Original holes closed: 1. New holes added: 1.
This is a decomposition: the added theorem is the strict bad-locus contradiction and Noetherian
stabilization subargument, while the delivered item combines it with the target's negated
existential using real Lean proof.

## No longer needed

Removed the unused direct proof imports for `DimensionAtPointFieldExtension`,
`DimensionSupremumLocalDimensions`, `FibreDimensionBoundedOpenUpstairs`, both reduced-induced
closed-subscheme modules, `AffineTransitionLimit`, and `GammaSpecAdjunction`; these belong to the
new core's planned proof and are not needed by the final implication itself. No existing target or
unit statement is bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement or definition was found to be false. The imported DAG proof is substantially longer
than the final Lean implication; its bad-locus construction is now represented by a named
intermediate node rather than an unfinished proof body.

## New nodes

`lem-weil-pbc-affine-limit-fibre-dimension-bound-core` records the bad-locus contradiction,
including the open bad loci, reduced closed subschemes, affine inverse limit nonemptiness, and
Noetherian stabilization of the residue-field fibre system. Its module is
`lean/Sheaf/AlgebraicGeometry/AffineLimitFibreDimensionBoundCore.lean`.

## Second reading by R9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
