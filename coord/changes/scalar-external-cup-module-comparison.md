# Scalar external cup module comparison

## Reason

Restore the returned scalar comparison modules and their named DAG statements.
The external comparison proof reduces its statement to the two prerequisite
comparison theorems.

## Old

The three delivered modules were absent from the sheaf-dag library after the
returned landing. No public declarations were available under these module names.

## New

The delivery adds `scalarCup_moduleCup_compatibility`,
`scalar_moduleCohomologyPullback_comparison`, and the proved
`scalarExternalCup_moduleComparison`, with the exact statements recorded in their
DAG nodes. No existing declaration is modified.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ScalarExternalCupModuleComparison | N2 | supplies the target reduction |
| Sheaf.AlgebraicGeometry.ScalarCupModuleCupCompatibility | unclaimed | supplies scalar cup comparison |
| Sheaf.AlgebraicGeometry.ScalarModuleCohomologyPullbackComparison | unclaimed | supplies pullback comparison |

## Status

landed 20261013T215607-L-899206 2026-10-13 (merge of deliver/N2/Sheaf.AlgebraicGeometry.ScalarExternalCupModuleComparison)
