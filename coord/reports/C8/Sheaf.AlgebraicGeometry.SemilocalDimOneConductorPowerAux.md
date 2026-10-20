## What changed

The Sheaf copy was withdrawn and is listed in `deleted.txt`. The official
`WeilConjectures.AlgebraicGeometry.SemilocalDimOneConductorPowerAux` twin remains the
source of `exists_finite_adjoin_with_jacobson_power`. The consumer had already been
adapted in the shared library: `WeilConjectures.AlgebraicGeometry.SemilocalDimOneConductorPower`
imports the twin directly, and no live Sheaf consumer remains.

## Proved and sorry left

There were zero sorries in the retired Sheaf stub; zero remain. The official twin is
unchanged and already proved.

## No longer needed

The retired Sheaf module and its old declaration/import closure are no longer needed.
The DAG node already points to the official twin, so no node dependency is removed here.

## Where the brief, the DAG or earlier work was wrong

The packet was stale because earlier landings had already emptied the Sheaf stub and
adapted its consumer. This delivery records the required final deletion.

## Second reading by C8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
