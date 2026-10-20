## What changed

Added `public import WeilConjectures.Algebra.Homology.KFlat` to
`Sheaf.AlgebraicGeometry.DerivedPullbackTensorUnitKFlat`.  The compatibility
module re-exports the adopted complete theorem, whose public signature uses
`CochainComplex.IsKFlatTensor`; the explicit public import makes that predicate
available to downstream modules importing the Sheaf path.  The adopted source
proof and all theorem signatures are unchanged.

The module compiles through `lcompile.py`.  A consumer probe importing only the
Sheaf path resolves both `CochainComplex.IsKFlatTensor` and
`AlgebraicGeometry.derivedPullback_tensor_unit_kFlat` and compiles.

## Proved and sorry left

The adopted theorem `AlgebraicGeometry.derivedPullback_tensor_unit_kFlat` is
already completely proved.  This delivery adds no declarations and leaves no
`sorry`s: 0 holes closed, 0 holes added, 0 split off.

## No longer needed

No proof imports or DAG nodes are removed.  The compatibility import remains
the shortest route to the complete adopted source proof.

## Where the brief, the DAG or earlier work was wrong

The rework queue retained this item after the compatibility module had already
been restored.  Its original quarantined implementation imported a second
`derivedPullback` construction and failed with an environment collision.  The
current module correctly reuses the adopted source theorem; the only missing
interface detail was that its K-flat predicate was not re-exported by the Sheaf
path.  No statement or mathematical route is changed.

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
