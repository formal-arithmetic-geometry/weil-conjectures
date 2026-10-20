# Sheaf.AlgebraicGeometry.EtaleCohomologyFilteredColimit

## Reason

Retire the duplicate Sheaf module in favor of its adopted upstream twin, as
assigned by coord/retire-items.tsv and the human's retirement instruction of
2026-10-20. The current shared sources have already retired the three consumers
listed in that table. No remaining Lean module imports the duplicate, and no
DAG node has its lean.module attached to it.

## Old

The module declares
`AlgebraicGeometry.Scheme.etaleCohomology_isColimit_of_isFiltered` and
`AlgebraicGeometry.Scheme.etaleModuleCohomology_isColimit_of_isFiltered`.
The abelian statement agrees with the upstream twin. The duplicate's module
statement accepts an index in Type (u + 1), whereas the upstream module
statement accepts an index in Type u. Neither declaration in the duplicate
has a sorry. No remaining consumer uses the larger-index duplicate statement.

## New

Withdraw lean/Sheaf/AlgebraicGeometry/EtaleCohomologyFilteredColimit.lean.
Use WeilConjectures.AlgebraicGeometry.EtaleCohomologyFilteredColimit for the
existing abelian and small-index module theorems. No replacement theorem,
statement change, definition change, or upstream edit is made.

## Users

A source scan of lean/Sheaf and lean/WeilConjectures finds no remaining import
of the withdrawn module. The three former consumers in coord/retire-items.tsv
are already absent as Sheaf modules; their upstream versions import the twin.
No consumer adaptation or additional claim is needed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleCohomologyFilteredColimit | A5 | Withdraw duplicate. |
| WeilConjectures.AlgebraicGeometry.EtaleLimitAffineDegreeZeroKernel | unchanged upstream | Already imports the twin; no edit. |
| WeilConjectures.AlgebraicGeometry.EtaleLimitCohomologyDegreeZeroDescent | unchanged upstream | Already imports the twin; no edit. |
| WeilConjectures.AlgebraicGeometry.PullbackIsoTorsionColimit | unchanged upstream | Already imports the twin; no edit. |

No target statement or target definition changes. The filtered-cohomology
node remains attached to the upstream target FreeSheaf module, as before.

## Status

landed 20261020T131932-L-1391234 2026-10-20 (merge of deliver/A5/Sheaf.AlgebraicGeometry.EtaleCohomologyFilteredColimit)
