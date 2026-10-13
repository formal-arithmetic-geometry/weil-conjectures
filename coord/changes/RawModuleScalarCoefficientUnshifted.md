# RawModuleScalarCoefficientUnshifted

## Reason
The coefficient-square proof requires a separately delivered unshifted comparison module,
which introduces the derived scalar comparison and its two prerequisite theorems.

## Old
No module existed in the repository.

## New
`Sheaf.AlgebraicGeometry.RawModuleScalarCoefficientUnshifted` provides
`RawModuleScalarComparison.derivedPullbackIso`,
`rawModuleScalar_derivedPullbackIso_commShift`, and
`rawModuleScalar_coefficient_unshifted`.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.RawModuleScalarCoefficientSquare | S2 | imports the module and uses all three declarations |

## Status

landed 20261013T234521-L-2167018 2026-10-13 (merge of deliver/S2/Sheaf.AlgebraicGeometry.RawModuleScalarCoefficientSquare)
