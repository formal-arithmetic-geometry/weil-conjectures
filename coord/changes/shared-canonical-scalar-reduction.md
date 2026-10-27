# WeilConjectures.scalarReductionExistence and scalarReductionExtension (withdrawn)

## Reason

The delivery proposed to redefine `scalarReductionExistence` as
`unrestrictedIntegralReductionExistence l E Y n` and `scalarReductionExtension` as
`unrestrictedIntegralReductionFunctor l E Y n` in the unclaimed module
`Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`, with a new public import of
`Sheaf.Paper.IntegralReductionTowerUnrestricted`, for elaboration speed only.

The independent reader withdrew this change (2026-10-26). Although the new bodies are
definitionally equal to the old ones, the change broke the published direct importer
`Sheaf.Paper.IntegralReductionTowerWellDefinedUnrestricted` (line 462,
`towerReduction_quasiIso`): its `simpa only [scalarReductionExtension]` now unfolds to
`unrestrictedIntegralReductionFunctor …` and no longer matches the type of
`(scalarReductionExistence l E Y n).choose_spec…`, a type mismatch. The adaptation is
not needed: the item `Sheaf.Paper.PointTransportConeComparisonDescent` compiles
(about 47 s, no error) against the published module.

## Old

Unchanged: the published module stays as it is.

## New

Unchanged: no declaration, body, import or attribute of
`Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction` changes.

## Users

None affected.

## Status

withdrawn
