# AlgebraicGeometry.Scheme.exists_irreducible_refinement

## Reason

The assigned Sheaf module is already proved with zero `sorry`s. The adopted source
library contains the same theorem in
`WeilConjectures.AlgebraicGeometry.IrreducibleLisseRefinement`, with the finite
locally constant predicate used by the Sheaf statement definitionally identified
with `IsLisseEtaleSheafOfSets`. Retire the duplicate and migrate its sole Sheaf
consumer to the adopted provider.

## Old

The duplicate provider was
`Sheaf.AlgebraicGeometry.IrreducibleLisseRefinement`, declaring
`AlgebraicGeometry.Scheme.exists_irreducible_refinement` with the lisse predicate
`IsLisseEtaleSheafOfSets`.
`Sheaf.AlgebraicGeometry.IrreducibleLisseStrata` imported that provider.

## New

`Sheaf.AlgebraicGeometry.IrreducibleLisseRefinement` is withdrawn through
`deleted.txt`. The consumer imports
`WeilConjectures.AlgebraicGeometry.IrreducibleLisseRefinement`, whose complete
`exists_irreducible_refinement` theorem is used unchanged. The DAG node is rebound
to this adopted declaration; no target statement or source-library declaration is
changed.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.IrreducibleLisseStrata | unclaimed | Replace its import of the withdrawn duplicate with the adopted source module; proof and statement remain unchanged. |
| WeilConjectures.AlgebraicGeometry.IrreducibleLisseStrata | source library | Already imports the adopted source module; unchanged. |

## Status

landed 20261021T012425-L-2188851 2026-10-21 (merge of deliver/Q2/Sheaf.AlgebraicGeometry.IrreducibleLisseRefinement)
