## What changed

Withdrew the duplicate module `Sheaf.AlgebraicGeometry.OpenUnionRestrictionComparisonDiagram`
through `deleted.txt`. Repointed the existing DAG node
`lem-sc-open-union-restriction-comparison-diagram` to the complete source declaration
`WeilConjectures.AlgebraicGeometry.Scheme.open_union_restriction_comparison_diagram`.
Added the retirement change record
`coord/changes/retire-open-union-restriction-comparison-diagram.md`.

The source theorem omits the unused `JW` and `JV` let bindings present in the Sheaf
copy. A scratch theorem with the original signature compiled by applying the source
twin, confirming definitional compatibility. No live Lean importer of the withdrawn
Sheaf module exists, so no consumer adaptation is needed.

## Proved and sorry left

The assigned module had zero `sorry`s before retirement and zero afterward. No holes
were closed, no holes were added, and no statements were split off. The complete
upstream theorem supplies the retained declaration.

## No longer needed

The duplicate Sheaf module and its private proof imports are pruned. The source twin,
its proof dependencies, and the DAG node remain needed by the open-union transport
route. No dependency node is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The item was queued as a retirement after its proof had already landed. The current
Sheaf copy is redundant: the source twin is complete and the only textual difference
in the theorem type is the pair of unused let bindings. The retirement inventory
records the copies as different because their historical dependency closures differed;
the direct theorem compatibility check shows that the mathematical statement is
preserved.

## Second reading by X3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
