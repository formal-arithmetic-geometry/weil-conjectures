## What changed

Updated the already-empty retired compatibility module's module documentation to
identify the official `WeilConjectures` declaration that owns the theorem and to
record the source and blueprint. No Lean declarations or imports were added.

## Proved and sorry left

The assigned retirement has zero original holes, zero holes closed, zero holes
added, and zero split-off holes. The module contains no declarations and no
`sorry`.

## No longer needed

No proof imports or DAG proof dependencies are needed because the duplicate
module is empty. The official theorem and all of its source dependencies remain
in `WeilConjectures`.

## Where the brief, the DAG or earlier work was wrong

The generic stage-3 brief describes filling a theorem proof, but the current
queue and retirement record assign this already-proved duplicate to retirement.
Its theorem is supplied by the official source-library twin, so restoring a
second public theorem would create a duplicate API.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
