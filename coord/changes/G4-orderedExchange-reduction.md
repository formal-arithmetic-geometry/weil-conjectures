# AlgebraicGeometry.Scheme.OrderedExchange.reduction

## Reason

Package the universal derived functor, counit and K-flat computation law in
`DerivedReductionModelData`. The previous nested existential choices caused
expensive repeated concrete type comparisons. The new model is chosen from the
proved `reductionData_exists`, and the original `reduction_exists` is recovered
from its fields. This changes the literal choice, rather than claiming definitional
equality of the selected functors. The universal property determines the pair up
to the unique counit-compatible natural isomorphism, exactly as for the former
selection. No arbitrary object is selected from a mere existence assertion.

## Old

```lean
def reduction (T : Scheme.{t}) : D (A := A) T ⥤ TD (A := A) T := (reduction_exists d T).choose
```

## New

```lean
def reduction (T : Scheme.{t}) : D (A := A) T ⥤ TD (A := A) T :=
  (reductionData d T).reduction
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.A1LisseSectionEvaluation | unclaimed | Textual match to another `reduction` API; no semantic change. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Textual match to another `reduction` API; no semantic change. |
| Sheaf.Paper.AdicPurityObjects | unclaimed | Textual match to another `reduction` API; no semantic change. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Textual match to another `reduction` API; no semantic change. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | Textual match to another `reduction` API; no semantic change. |
| Sheaf.Paper.CoefficientTowerShriekInterfaces | unclaimed | Textual match to another `reduction` API; no semantic change. |
| Sheaf.Paper.CoefficientTowerTransitionCompatibility | unclaimed | Textual match to another `reduction` API; no semantic change. |
| Sheaf.Paper.CompactSupportProjectionFormula | unclaimed | Textual match to another `reduction` API; no semantic change. |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | unclaimed | Textual match to another `reduction` API; no semantic change. |
| Sheaf.Paper.CompletedExchangeCoherence | S9 | Textual match to another `reduction` API; no semantic change. |
| Sheaf.Paper.CompletedProjectionCoherence | V1 | Textual match to another `reduction` API; no semantic change. |
| Sheaf.Paper.CompletedPullbackUnitTower | D8 | Textual match to another `reduction` API; no semantic change. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | Textual match to another `reduction` API; no semantic change. |
| Sheaf.Paper.CompletedTensorHomTranspose | unclaimed | Textual match to another `reduction` API; no semantic change. |
| Sheaf.Paper.ConstantExtensionCompactComparison | unclaimed | Textual match to another `reduction` API; no semantic change. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData | unclaimed | Textual match to another `reduction` API; no semantic change. |
| Sheaf.Paper.DiagonalTowerTraceCoefficients | unclaimed | Textual match to another `reduction` API; no semantic change. |
| Sheaf.Paper.FrobeniusCompactSupportExchange | unclaimed | Textual match to another `reduction` API; no semantic change. |
| Sheaf.Paper.FrobeniusFixesUnitSection | unclaimed | Textual match to another `reduction` API; no semantic change. |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | unclaimed | Textual match to another `reduction` API; no semantic change. |
| Sheaf.Paper.IntegralCompactSupportCoefficientComparison | unclaimed | Textual match to another `reduction` API; no semantic change. |
| Sheaf.Paper.IntegralDirectImageTower | M2 | Textual match to another `reduction` API; no semantic change. |
| Sheaf.Paper.IntegralExceptionalInverseImage | unclaimed | Textual match to another `reduction` API; no semantic change. |
| Sheaf.Paper.IntegralPointTransportTowerPowers | unclaimed | Textual match to another `reduction` API; no semantic change. |
| Sheaf.Paper.OrderedExchangeCoefficientComparison | unclaimed | Same canonical reduction and representative equations; replace the expanded derived-limit complex unit by the existing library API, with its exact original formula proved generically, to repair compile time. |
| Sheaf.Paper.ProEtaleConstantReductionTower | G4 | Same universal constructions and normalized maps; proofs updated. |
| Sheaf.Paper.ProperCoincidenceFrobenius | unclaimed | Textual match to another `reduction` API; no semantic change. |
| Sheaf.Paper.ProperSectionsSemilinearGerms | unclaimed | Textual match to another `reduction` API; no semantic change. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | Textual match to another `reduction` API; no semantic change. |
| Sheaf.Paper.QcqsCompactSupportRealization | unclaimed | Textual match to another `reduction` API; no semantic change. |
| Sheaf.Paper.RationalSmoothPurityCanonical | unclaimed | Textual match to another `reduction` API; no semantic change. |
| Sheaf.Paper.SfCbcCompactSupportCompositionLimit | unclaimed | Textual match to another `reduction` API; no semantic change. |
| Sheaf.Paper.SfIntegralPullbackLinearAdjunction | unclaimed | Textual match to another `reduction` API; no semantic change. |
| Sheaf.Paper.SixFunctorOperationDatumStages | unclaimed | Textual match to another `reduction` API; no semantic change. |
| Sheaf.Paper.SystemOperationExchangeRealization | unclaimed | Textual match to another `reduction` API; no semantic change. |
| Sheaf.Paper.TowerClassChern | unclaimed | Textual match to another `reduction` API; no semantic change. |
| Sheaf.Paper.TowerClassDiagonal | unclaimed | Textual match to another `reduction` API; no semantic change. |
| Sheaf.Paper.TwistFrobeniusScalar | unclaimed | Textual match to another `reduction` API; no semantic change. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Textual match to another `reduction` API; no semantic change. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Textual match to another `reduction` API; no semantic change. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed | Textual match to another `reduction` API; no semantic change. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | unclaimed | Textual match to another `reduction` API; no semantic change. |
| Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison | unclaimed | Textual match to another `reduction` API; no semantic change. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | unclaimed | Textual match to another `reduction` API; no semantic change. |
| Sheaf.SixFunctors.FiniteExceptional | unclaimed | Textual match to another `reduction` API; no semantic change. |
| Sheaf.SixFunctors.GeneratorReductionStatement | unclaimed | Textual match to another `reduction` API; no semantic change. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | unclaimed | Textual match to another `reduction` API; no semantic change. |
| Sheaf.SixFunctors.IntegralCompactificationComparisonBridge | unclaimed | Textual match to another `reduction` API; no semantic change. |
| Sheaf.SixFunctors.IntegralCompactificationSystemRealization | unclaimed | Textual match to another `reduction` API; no semantic change. |
| Sheaf.SixFunctors.IntegralOperationShiftData | unclaimed | Textual match to another `reduction` API; no semantic change. |
| Sheaf.SixFunctors.IntegralRealizationRecursion | unclaimed | Textual match to another `reduction` API; no semantic change. |
| Sheaf.SixFunctors.IntegralSystemCanonicalBridge | unclaimed | Textual match to another `reduction` API; no semantic change. |
| Sheaf.SixFunctors.IntegralSystemExpressionDomain | unclaimed | Textual match to another `reduction` API; no semantic change. |
| Sheaf.SixFunctors.IntegralVerdier | V2 | Textual match to another `reduction` API; no semantic change. |
| Sheaf.SixFunctors.OpenFactorCoherence | unclaimed | Textual match to another `reduction` API; no semantic change. |

This table includes every textual hit from `tools/downstream.py --uses`;
name collisions are identified above. No adopted source-library file is changed. Direct
importers and the coefficient-comparison consumer are checked against the new
module. Statements involving the repaired universal pair retain their intended
meaning: the constant coefficient rings, finite quotients, strict transitions,
universal properties, normalizing equations and completion unit are unchanged.
Any target whose statement depends on a changed definition must undergo the
required statement review again. No target signature is changed.

## Status

landed 20261020T221158-L-4154121 2026-10-20 (merge of deliver/G4/Sheaf.Paper.ProEtaleConstantReductionTower)
