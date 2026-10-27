## What changed

Added the proof-only module `Sheaf.AlgebraicGeometry.SquareSectionUnitForward`, which
states the forward normalized square comparison before the final endpoint inverse. The
assigned module imports this intermediate statement and proves
`AlgebraicGeometry.squareSectionUnit_cancellation` by postcomposing with the endpoint
isomorphism and cancelling its hom/inverse pair. The original target statement and
public imports are unchanged.

## Proved and sorry left

Closed the original hole:

- `AlgebraicGeometry.squareSectionUnit_cancellation`.

Added one strictly smaller split-off statement with one documented `sorry`:

- `AlgebraicGeometry.squareSectionUnit_forward`, in
  `lean/Sheaf/AlgebraicGeometry/SquareSectionUnitForward.lean`, node
  `lem-weil-pbc-square-section-unit-forward`.

No definition contains a `sorry`.

## No longer needed

No imports were removed. The target proof directly uses only the new forward node; the
forward node retains the declared normalized mate, local Leray, inverse-open, and
injective endpoint dependencies needed for the unresolved calculation.

## Where the brief, the DAG or earlier work was wrong

The original DAG proof plan bundled the evaluated normalized-square calculation and the
final inverse endpoint cancellation into one statement. The latter is an elementary
categorical cancellation once the forward equation is isolated, so the forward equation
is recorded as a strictly smaller split-off node. The assigned target statement is
unchanged.

## New nodes

`lem-weil-pbc-square-section-unit-forward` records the forward normalized square
comparison, ending at the hom of `squareInjectiveLocalComparison` for `k`; the assigned
target follows by composing with its inverse. Its Lean declaration is
`AlgebraicGeometry.squareSectionUnit_forward` in
`lean/Sheaf/AlgebraicGeometry/SquareSectionUnitForward.lean`.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
