## Reason

The target proof required two independent mathematical steps: constructing the
pullback-compatible completed-to-native map family, and proving that normalized
coefficient presentations induce the same integral map. They are recorded as named
intermediate theorems so the target proof combines strictly smaller obligations.

## Old

`native_completed_coefficient_change` was an unproved theorem with no map construction
or presentation-independence declarations available to its proof.

## New

The target theorem is proved from `native_completed_coefficient_change_data` and
`coefficientPresentation_integralMap_eq`. The two new declarations are in
`Sheaf.Paper.NativeCompletedCoefficientChangeData` and
`Sheaf.Paper.CoefficientPresentationIntegralMapIndependence`.

## Users

`Sheaf.Paper.NativeCompactSupportFiniteComparison` consumes the target theorem. Its
signature and use remain unchanged. The new helper modules are imported only by the
target module.

## Status

The target theorem compiles with no sorry. The two helper theorem proofs remain named
stage-3 sorries and have corresponding DAG nodes.
