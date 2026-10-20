## What changed

This item is an approved retirement of the duplicate Sheaf module. The
withdrawn file is listed in `deleted.txt`; the official
`WeilConjectures.AlgebraicGeometry.AffinePrincipalCoverQuasiIsoDetection`
module remains the sole implementation of the theorem. The DAG node already
records that official declaration and the current tree has no Sheaf importers.

## Proved and sorry left

No Lean theorem was changed. The retired duplicate has zero sorries and the
official twin is already proved. This retirement closes no new sorry because
the item is listed in `coord/retire-items.tsv` and was previously retired by
V2.

## No longer needed

The duplicate Sheaf module, its former duplicate proof dependencies, and its
old Sheaf consumer are no longer needed. The official WeilConjectures proof
and its imports remain in place.

## Where the brief, the DAG or earlier work was wrong

The dispatch queue still listed this already-retired duplicate as a stage-3
retirement item. The current DAG and source tree are consistent: the node's
`lean` record points to the official twin, while the Sheaf file is an empty
withdrawal stub. No mathematical statement or unit route is changed.

## Second reading by D7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
