# standard_resolution_formula compiler options

## Reason
The proof of `Sheaf.AlgebraicGeometry.ModuleCohomologyExtStandardResolutionFormula`
requires deterministic elaboration and a larger heartbeat allowance for its fixed
resolution interfaces. Preflight classifies these compiler commands as an interface
change, although every existing declaration signature and visibility is preserved.

## Old
The module used its original backward-definitional-equality options and the default
asynchronous elaboration and heartbeat allowance. `standard_resolution_formula`
was a named theorem with `sorry`.

## New
The module adds `set_option Elab.async false` and a declaration-scoped
`set_option maxHeartbeats 600000 in`, with an explanatory comment. The 60-second
compilation deadline is unchanged. Two private proof imports supply the module
sections factorization and the smaller Ext sections calculation. No definition,
instance, statement, universe, or public import changes.

## Users
| module | group holding it | effect |
|---|---|---|
| `Sheaf.AlgebraicGeometry.ModuleCohomologyExtResolutionNormalization` | unclaimed | Identical theorem signature; no adaptation required. |

`Sheaf.AlgebraicGeometry.ModuleCohomologyExtResolutionNormalization` imports the
item and uses `standard_resolution_formula`; it requires no adaptation because the
signature is identical. Searching both library roots for the theorem and its module
import found no other user. No module held by another group is adapted.

## Status
landed 20261014T071230-L-3198698 2026-10-14 (merge of deliver/C1/Sheaf.AlgebraicGeometry.ModuleCohomologyExtStandardResolutionFormula)
