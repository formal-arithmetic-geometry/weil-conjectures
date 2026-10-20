## What changed

Restored `lean/Sheaf/AlgebraicGeometry/AffineSpectrumCounitSquare.lean` from its
quarantine archive and added the public statement dependency
`Sheaf.Algebra.Homology.KFlat`. This repairs the recorded missing
`CochainComplex.IsAcyclicTensorKFlat` error without altering the statement or proof
of `AlgebraicGeometry.SingleComplexBaseChange.affineSpectrum_counit_square`.

The restored module compiles through `lcompile.py` (46.8 seconds, exit code 0).
Change record: `coord/changes/N3-affine-spectrum-counit-kflat-import.md`.

## Proved and sorry left

Zero original holes, zero holes closed, zero holes added, zero holes left.
The complete archived proof of
`AlgebraicGeometry.SingleComplexBaseChange.affineSpectrum_counit_square`
is preserved (node `lem-pc-affine-spectrum-counit-square`). This is a compile
repair of a quarantined module, not a decomposition or a new proof claim.

## No longer needed

None. No imports, declarations, modules, or DAG dependencies are removed.
The existing composition-counit proof route and the quarantined parent dependency
remain intact. No source-library declaration is modified or withdrawn.

## Where the brief, the DAG or earlier work was wrong

The upstream sync replaced the transitive K-flat interface with `IsKFlatTensor`,
while this retained project theorem still uses `IsAcyclicTensorKFlat`. The original
module consequently needed an explicit public import of its statement's predicate.
The rework record correctly identified this missing dependency. No mathematical
statement repair is required; the node's Lean attachment and proof plan stay unchanged.

## Second reading by N3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
