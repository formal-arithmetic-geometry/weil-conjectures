## What changed

Completed the listed retirement of Sheaf.AlgebraicGeometry.HigherDirectImageRawDiagram.
Its current source is a declaration-free re-export of the upstream module. Withdraw
it with deleted.txt and change the sole direct importer,
Sheaf.AlgebraicGeometry.RawModuleScalarPullbackComparison, to publicly import that
upstream module directly. Only that import line changes in the consumer.
The two existing DAG attachments remain upstream; their lean.note records retirement.
Change record: coord/changes/V1-retire-raw-diagram-shim.md.

## Proved and sorry left

The assigned module has zero sorries and no declarations before retirement.
Holes closed: 0 of 0. Holes added: 0. Split off: 0. Sorries left: none in any
modified Lean module. The canonical upstream functoriality theorem and explicit
raw diagram, functor and cocone constructions are preserved verbatim.
This is retirement of a duplicate module path, not a new proof or decomposition.

## No longer needed

Pruned module: Sheaf.AlgebraicGeometry.HigherDirectImageRawDiagram.
Removed import: public import Sheaf.AlgebraicGeometry.HigherDirectImageRawDiagram
in RawModuleScalarPullbackComparison, replaced by the upstream module re-exported
by the shim. No mathematical node or proof dependency is pruned. The DAG parents
and unit route retain the same mathematical statements and dependencies.
Exact-import searches include quarantined modules; the only direct user is adapted.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes an item with holes and five prior splits.
The current source has already been canonicalized by reviewed D2 work; both
DAG nodes point to WeilConjectures.AlgebraicGeometry.HigherDirectImageRawDiagram.
coord/retire-items.tsv explicitly lists this item for retirement, so this packet
completes that listed repair with its actual zero-hole count. There is no rework
row or current V1 return. No declaration is removed from the adopted source tree.

## Second reading by V1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
