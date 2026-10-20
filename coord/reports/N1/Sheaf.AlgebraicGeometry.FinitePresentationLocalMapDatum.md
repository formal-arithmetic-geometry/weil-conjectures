## What changed

The module was already fully proved and contained zero `sorry`s.  The retirement queue
lists it as a duplicate of the proved upstream twin, so I withdrew
`lean/Sheaf/AlgebraicGeometry/FinitePresentationLocalMapDatum.lean` via `deleted.txt`.
The DAG node now points to
`WeilConjectures.AlgebraicGeometry.FinitePresentationLocalMapDatum`; its theorem is
stronger because it omits the unused Noetherian instance and therefore specializes to
the node statement.  The two source consumers already import that upstream module.

## Proved and sorry left

Zero holes were present before the retirement, zero holes were closed, and zero holes
were added.  The upstream declaration is complete and introduces no `sorry`.

## No longer needed

The duplicate Sheaf module and its private imports are pruned.  No proof dependency or
unit route is removed: the node retains its existing proof dependencies, now attached
to the upstream declarations.  No consumer module needed adaptation because both
current consumers already import the upstream twin.

## Where the brief, the DAG or earlier work was wrong

The generic item brief describes a module containing a `sorry`, but this module's proof
was already landed.  The current retirement queue explicitly marks the Sheaf copy for
withdrawal.  The source theorem drops only an unused Noetherian hypothesis, so the
retirement preserves the mathematical statement and the unit route.

## New nodes

None.

Change record: `coord/changes/retire-finite-presentation-local-map-datum.md`.

## Second reading by N1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
