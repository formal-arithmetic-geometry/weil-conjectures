## What changed

Restored `Sheaf.AlgebraicGeometry.SingleComplexOpenRestrictedCounitCancellation`
as a public re-export of the existing upstream module with the same suffix.
The upstream theorem has the exact same signature and complete proof body as the
quarantined declaration; both were compared verbatim. The existing DAG node
`lem-pc-k3-open-restricted-counit-cancellation` now attaches to that upstream
declaration. Its mathematical statement, proof steps and proof dependency stay.
No source-library file is changed and no consumer needs adaptation.
The restored module compiles cleanly in 2.3 seconds. A separate import probe
finds the theorem through the restored module and reports exactly `propext`,
`Classical.choice`, and `Quot.sound` as its axioms (2.4 seconds).

Change record:
`coord/changes/S8-open-restricted-counit-reducibility-rework.md`.

## Proved and sorry left

This is a compilation repair with zero original holes. The existing complete
upstream proof of
`AlgebraicGeometry.singleComplexOpen_restricted_counit_cancellation`
is reused. Holes closed: 0. Holes added: 0. Sorries left in the restored module: 0.
No statements are split off and no new theorem or assumption is introduced.

## No longer needed

The duplicate local theorem and its two private categorical helpers are replaced
by the existing upstream proof. The former direct imports of
`WeilConjectures.AlgebraicGeometry.SingleComplexOpenPinnedComposition`,
`WeilConjectures.AlgebraicGeometry.SingleComplexOpenPinnedAdjunction`,
`WeilConjectures.AlgebraicGeometry.OpenPinnedSingleDegreeZeroCounitIso`, and
`WeilConjectures.AlgebraicGeometry.OpenPinnedCounitHomotopyRestriction` are removed
from the wrapper; the first three remain publicly available through the upstream
module. No dependency node or module is pruned: the upstream proof still uses
`open_pinned_counit_homotopy_restriction` through its private import.

## Where the brief, the DAG or earlier work was wrong

The assigned item is a zero-hole rework item whose source is quarantined, rather
than an unfinished proof at its original `lean/` path. Upstream now declares
`derivedPullback` with `irreducible_def`, invalidating the old local attribute.

Removing that redundant attribute alone compiles cleanly in 42.5 seconds and
passes a delivery dry run, but the subsequent submission compile times out at
60 seconds. The exact proof is already available upstream, so reuse removes the
unnecessary duplicate elaboration. This keeps the full categorical argument and
the same treatment of empty opens and zero complexes. No compilation limit is
raised and no definition changes. There are no current importers of the
quarantined `Sheaf` module to adapt.

## Second reading by S8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
