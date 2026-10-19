# Sheaf.Paper.PurityFiniteKummerLevel

## Reason
The retained proof prunes two public imports that were used only by the unfinished geometric
route. The module also adds the named geometric comparison theorem required to carry that
remaining result as a separate stage-3 item.

## Old
The module publicly imported `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison` and
`Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted` and had only the parent theorem.

## New
Those imports are removed because the retained arithmetic proof does not use them. The module
adds `finiteKummerLevel_geometric`, whose proof is intentionally split off as a named theorem.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.PurityConventions | unclaimed | recheck imports after the pruning |

## Status
landed 20261019T192811-L-1869624 2026-10-19 (merge of deliver/P1/Sheaf.Paper.PurityFiniteKummerLevel)
