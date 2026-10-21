## What changed

Withdrew the declaration-free compatibility shim
`Sheaf.AlgebraicGeometry.HigherDirectImageRawTriangleAdjunct`, as requested by its
`retire` queue row and the explicit retire inventory. The canonical upstream theorem
`AlgebraicGeometry.Etale.higherDirectImageRawTrianglePullback_adjunct` and all its proof
dependencies are retained unchanged. No current Lean source imports the withdrawn shim;
the former consumer now re-exports the upstream transition-to-hom core.
Change record: `coord/changes/M1-retire-raw-triangle-adjunct-shim.md`.

## Proved and sorry left

The item has zero declarations and zero `sorry`s. Holes closed: 0 of 0. Holes added: 0.
No statements were split off. Its upstream theorem already has a complete proof.
The compatibility module compiled cleanly before withdrawal (4.1 seconds).

## No longer needed

Pruned `Sheaf.AlgebraicGeometry.HigherDirectImageRawTriangleAdjunct`. It is a redundant
re-export of `WeilConjectures.AlgebraicGeometry.HigherDirectImageRawTriangleAdjunct`.
No other module or node is pruned. The node `sbc-lem-module-raw-triangle-adjunct` already
points upstream and remains a proof dependency of the transition-to-hom core; its proof
and the unit route are preserved. No consumer import rewrite is needed in the current
source, including the historical inventory consumer.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief does not mention that the current queue classifies this as a
retirement item. The retire inventory's historical Sheaf consumer has since become an
upstream re-export too. An initial verification-only packet did not implement the required
retirement; this packet supplies the actual withdrawal. No mathematical statement or DAG
route was changed, and no proof progress is claimed for the existing upstream theorem.

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
