## What changed

Withdrew `lean/Sheaf/AlgebraicGeometry/Modules/ExteriorSheafFullOpenIso.lean`.
The retirement record identifies it as a duplicate Sheaf twin of the already proved
upstream `WeilConjectures.AlgebraicGeometry.Modules.ExteriorSheafFullOpenIso`.
The upstream declaration is retained unchanged and remains the implementation used by
`WeilConjectures.AlgebraicGeometry.ConstantRankExteriorDerivedComparison`.

No live Sheaf module imports the withdrawn module, so no consumer adaptation is needed.
The DAG node is retained; retirement removes only this duplicate module.
See change record `coord/changes/retire-exterior-sheaf-full-open-iso-v4.md`.

## Proved and sorry left

The withdrawn module had no remaining `sorry`; it is retired under the explicit
`coord/retire-items.tsv` entry rather than proved again. No holes were closed and no
holes were added.

## No longer needed

The withdrawn Sheaf module and its proof-only imports are no longer needed. The
upstream module and its declaration remain needed by the retained source consumer.
No DAG node is deleted.

## Where the brief, the DAG or earlier work was wrong

The earlier proof delivery was valid when the duplicate Sheaf module was active. The
later twin-retirement synchronization superseded that route: the upstream declaration
is now the retained API, so keeping this duplicate would preserve redundant public
surface and an obsolete dependency chain.

## Second reading by V4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
