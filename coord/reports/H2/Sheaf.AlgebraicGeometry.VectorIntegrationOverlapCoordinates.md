## What changed

Proved `AlgebraicGeometry.Etale.vectorIntegration_overlap_coordinates` in
`Sheaf.AlgebraicGeometry.VectorIntegrationOverlapCoordinates`, preserving its statement,
its original docstring and its public imports. All added helpers are private and proved.
No other existing Lean module changed.

Constructed the restricted module frame and proved naturality of its basis sections,
symmetric-algebra coordinates, forward trivialization and inverse chart. On a common
open, applied the existing `VectorBundleZeroSection.transition_spec` with reversed frames,
transported the transposed inverse matrices along `U.topIso.inv`, and used
`AffineSpace.hom_ext` to identify the coordinate maps. Cancelling the forward
trivializations gives the inverse-chart relation. Applying this relation to the two
restricted frames proves the original theorem. Updated the item's node proof to describe
these steps; its four declared proof dependencies are retained.

The module compiled cleanly through `lcompile.py` in 22.9 seconds, without warnings.
The proof covers rank zero, empty opens and non-affine opens without new hypotheses.

## Proved and sorry left

Closed the sole original hole in
`AlgebraicGeometry.Etale.vectorIntegration_overlap_coordinates`
(node `lem-amb-vector-integration-overlap-coordinates`).

Holes closed: 1. Holes added: 0. Holes left in the item: 0. Split-off statements: 0.
This is a proof, not a decomposition. No definition contains a hole.

## No longer needed

No original imports, declared dependency nodes or modules were removed. All four original
proof dependencies are used. Trial direct imports of
`Mathlib.CategoryTheory.Adjunction.Limits`, `Mathlib.Algebra.Category.ModuleCat.Sheaf.Free`
and `Mathlib.AlgebraicGeometry.Modules.Sheaf` were removed after compilation showed the
original public import already exposes the necessary API. This does not prune those
modules from the project dependency closure.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The existing transition theorem already provides
the same-open coordinate calculation on arbitrary opens. The remaining restriction
coherence was proved locally rather than split off again. The unit route, statements,
definitions and public interfaces are unchanged.

## Second reading by H2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
