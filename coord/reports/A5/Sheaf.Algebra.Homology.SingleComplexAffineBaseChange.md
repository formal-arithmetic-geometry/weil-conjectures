## What changed

Restored `lean/Sheaf/Algebra/Homology/SingleComplexAffineBaseChange.lean` from
`quarantine/Sheaf/Algebra/Homology/SingleComplexAffineBaseChange.lean`, as required
by the current rework row. Replaced its obsolete public import of
`Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition` with
`WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition`.
Both other imports, the theorem signature and the complete proof are unchanged.
The affine theorem still specializes `singleComplexBaseChangeQcqsInduction` to
the four spectrum maps. That induction theorem uses the separate affine Core
criterion, so this does not introduce a circular Lean dependency.

The restored module compiled cleanly through `lcompile.py` in 1.8 seconds.
Change record: `coord/changes/A5-single-complex-affine-upstream-import.md`.
No source-library edits, consumer adaptations, new declarations or definition
changes are included. No target statement or meaning changes.

## Proved and sorry left

This is the assigned quarantine/import repair, with zero original holes.
`AlgebraicGeometry.singleComplexAffineBaseChange` retains its complete proof.
Holes closed: none (0 of 0). Holes added: none. Sorries left in the delivered
module: none. Split-off statements: none. This is a repair, not new proof progress.

## No longer needed

Removed the obsolete direct import
`Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition`, now an empty
withdrawn module. Its actual declarations come from the adopted upstream module.
No mathematical dependency, node or module is withdrawn or claimed pruned. The
coordinate/cohomology argument in the item's recorded DAG proof remains needed
by `singleComplexAffineBaseChangeCore`, used by the qcqs induction theorem.
The item attachment and all parent dependencies are preserved.

## Where the brief, the DAG or earlier work was wrong

The rework row records a duplicate `AlgebraicGeometry.derivedPullback` caused by
mixing Sheaf and adopted upstream implementations after the source sync. The
current old stalk-condition module has since been retired to an empty module;
the explicit import is corrected to the actual upstream provider. The archive
was restored, not deleted or replaced by an empty module.
The item has no current A5 return entry. Its DAG still records the underlying
affine coordinate proof; the archived wrapper proof and its existing route are
unchanged, so no DAG edits are necessary for this import repair.

## Second reading by A5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
