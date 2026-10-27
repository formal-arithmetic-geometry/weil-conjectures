# unrestrictedIntegralReductionFunctor / unrestrictedIntegralComplexFunctor (withdrawn)

## Reason

The delivery first annotated the codomain of `unrestrictedIntegralReductionFunctor` as
`SheafOfModules (derivedChangeRingIndependentCoefficients … (integralCoefficientCommRingSheaf l E Y n))`
and gave `unrestrictedIntegralComplexFunctor` an explicit type. The reviewer withdrew both edits
(2026-10-24): the new codomain is only definitionally, not reducibly, equal to
`SheafOfModules (integralCoefficientSheaf l E Y n)`, and `Sheaf.Paper.IntegralOperationsWellDefined`
(held by S4) then fails at line 937 (`failed to synthesize
(MonoidalCategory.curriedTensor (integralOperationsFiniteModules l E W n)).PreservesZeroMorphisms`,
and `integralOperationsTotalTensorSection` is not defined). The item compiles against the published,
unchanged module, so neither edit is needed.

## Old

Unchanged.

## New

Unchanged: `lean/Sheaf/Paper/IntegralReductionTowerUnrestricted.lean` is delivered identical to the
published module.

## Users

None affected; no declaration of the module changes.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralReductionTowerUnrestricted | unclaimed | No change. |

## Status

withdrawn
