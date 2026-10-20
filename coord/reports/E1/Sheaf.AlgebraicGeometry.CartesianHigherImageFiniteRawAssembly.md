## What changed

The Sheaf assembly module was already an empty withdrawn stub from the earlier
V3 retirement landing. I retained that zero-declaration state and updated its
withdrawal marker to identify the official replacement,
`WeilConjectures.AlgebraicGeometry.CartesianHigherImageFiniteRawAssembly`.

The three consumers named by the retirement row are already the official
upstream modules in the current library:

- `WeilConjectures.AlgebraicGeometry.CartesianHigherImageFiniteRawClassVanishing`
- `WeilConjectures.AlgebraicGeometry.CartesianRawClassChartNaturality`
- `WeilConjectures.AlgebraicGeometry.CartesianRawClassChartRepresentative`

Their imports and theorem calls use the upstream assembly API. No Sheaf
consumer source remains to adapt, and no upstream or target declaration is
changed.

## Proved and sorry left

The assigned module has zero declarations and zero sorries before and after
this delivery. No mathematical holes were closed or added. This is a
retirement reconciliation after the earlier landing, with the official twin
already in use by all listed consumers.

## No longer needed

The Sheaf assembly copy has no declarations and no Lean importers. The current
DAG contains no `lean.module` attachment to it. The official upstream assembly
and the three official consumer modules remain in place. The prior retirement
change record is `coord/changes/retire-cartesian-higher-image-finite-raw-assembly.md`.

## Where the brief, the DAG or earlier work was wrong

The queue and retirement row still list the pre-retirement Sheaf consumers,
but the earlier V3 landing had already switched those consumers to
`WeilConjectures` modules and emptied this Sheaf copy. The initial required dry
run consequently reported `FAILED: nothing is proved`. The current packet
keeps the module empty and records the official twin in its withdrawal marker,
which gives the delivery tool the required changed item while preserving the
already-landed retirement state.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
