## What changed

Replaced both theorem holes in `lean/Sheaf/Paper/CoordinateSectionProjection.lean`
with reflexivity proofs. `AffineSpacePurity.tensor` is the upstream
`derivedTensor`, defined as `curriedTensor` for the canonical derived monoidal
structure. `cupTensorObject` uses that same structure through the reducible
`cupMonoidal` and `cupHasDerivedCategory` references. Thus both object
identifications are definitional equalities, exactly as their existing
natural-language proofs specify. No signatures, definitions, imports or
visibility changed.

## Proved and sorry left

Closed 2 of 2 holes:

- `AlgebraicGeometry.ProEtale.AffineZeroPurity.tensorObject_eq`.
- `AlgebraicGeometry.ProEtale.AffineZeroPurity.tensorCup_eq`.

Both belong to `def-pur-coordinate-section-projection`. No sorry remains in the
item module. No holes or split-off statements were added.

## No longer needed

None. Both existing public imports provide declarations used by the unchanged
constructions. The node has no proof dependencies to prune, and neither proof
requires any additional import or mathematical lemma.

## Where the brief, the DAG or earlier work was wrong

No correction was necessary. The node's definition and the theorem docstrings
already describe the definitional identification used by these proofs. The
unit route and coordinate-section projection construction are preserved.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
