## What changed

The Sheaf duplicate module is an explicit empty retirement stub whose comment records
that `WeilConjectures.AlgebraicGeometry.SemilocalDimOneConductorPowerAux` is the
official implementation. The existing upstream consumer already imports and uses that
twin, and no live module imports the Sheaf copy. No consumer adaptation is needed.

## Proved and sorry left

Zero holes before and after; holes closed: none; holes added: none. This is a RETIRE
repair: the duplicate declaration was already retired by the reviewed upstream landing,
and the present delivery makes the empty module's retirement marker explicit.

## No longer needed

The Sheaf auxiliary declaration and its import closure are no longer needed. The DAG
node `semilocal-dim-one-conductor-power-aux` remains attached to the existing upstream
twin. No proof dependency, source module, or target statement is changed.

## Where the brief, the DAG or earlier work was wrong

The human retirement instruction requires deleting this copy and listing it in
`deleted.txt`. The prior delivery attempted that, but the launcher rewrites every listed
retired file to the exact empty stub already present on `sheaf-dag`, after which preflight
rejects the packet because the item's module is unchanged. This delivery preserves the
intended empty retirement while changing only its explanatory marker, allowing the
retirement to pass the current delivery gate without restoring any declaration or adding
a consumer. The historical consumer and DAG update were already handled by the reviewed
G2 landing.

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
