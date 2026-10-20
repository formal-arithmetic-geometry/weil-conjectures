## What changed

Revalidated the current retirement state of
`Sheaf.AlgebraicGeometry.AffinePrincipalCoverQuasiIsoDetection`. The Sheaf twin is
already an empty withdrawn module; the retained theorem is the proved
`WeilConjectures.AlgebraicGeometry.AffinePrincipalCoverQuasiIsoDetection` declaration,
and the DAG node already points to that official implementation. No Lean declaration
or theorem signature is changed in this packet.

## Proved and sorry left

The assigned module has zero declarations and zero `sorry`s. The retained official twin
has its original theorem proved. This packet closes 0 of 0 local sorries, adds 0, and
splits off 0.

## No longer needed

The duplicate Sheaf implementation and all of its former proof imports are no longer
needed. The official WeilConjectures module supplies the theorem used by the retained
consumer. No DAG node or unit-level route is removed.

## Where the brief, the DAG or earlier work was wrong

The incoming brief describes the former holed Sheaf implementation, but the current
shared base already contains the reviewed V2 retirement and its empty stub. Repeating
the old proof would duplicate an implementation that the current node intentionally
retains upstream.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
