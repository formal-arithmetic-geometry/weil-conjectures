## What changed

Retired `lean/Sheaf/AlgebraicGeometry/OverlapPairRefinementPersistence.lean` in
favour of the adopted upstream module
`WeilConjectures.AlgebraicGeometry.OverlapPairRefinementPersistence`. The upstream
module contains the same public declaration
`AlgebraicGeometry.overlap_pair_map_refinement_persistence` and the same recorded
statement. The Sheaf file is listed in `deleted.txt`, and the DAG node now points
to the upstream declaration. No upstream file or target statement was changed.

The source tree has no remaining Lean import of the Sheaf copy. The former Sheaf
pair-square transport consumer is already an empty withdrawn module, and the
remaining finite-presentation consumer is the upstream module, which already
imports the upstream persistence theorem.

## Proved and sorry left

Holes closed: 0. Holes added: 0. The retired module and its adopted upstream twin
are both sorry-free. No theorem was re-proved in this delivery; this is a duplicate
retirement with the existing complete upstream proof retained.

## No longer needed

Pruned `Sheaf.AlgebraicGeometry.OverlapPairRefinementPersistence` and its duplicate
private helper/proof imports. No live Lean consumer or proof dependency is removed;
the DAG attachment is redirected to the upstream declaration. The public persistence
statement and its unit route are unchanged.

## Where the brief, the DAG or earlier work was wrong

The item was queued as a stage-3 retirement even though the Sheaf copy had already
been proved and contained no `sorry`. The retirement table's current upstream twin
is complete and has the same public theorem. The old Sheaf attachment was stale
after the upstream sync and duplicate-retirement waves; repointing the node is the
correct repair.

The retirement is recorded in
`coord/changes/overlap-pair-refinement-persistence-retirement.md`.

## Second reading by H3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
