# Sheaf.Paper.IntegralMatrixFunctionsPullback

## Reason

The returned delivery duplicated this private theorem and its private matrix-entry calculation. Expose the existing theorem, retaining its statement and proof verbatim, so the item can import and use it. The matrix-entry calculation remains private in its original module. No definition changes.

Both the original and changed module are checked against current shared sources. This module is unclaimed. No target statement or target-used definition changes meaning; no target statement review is reopened. Zero ranks and empty schemes remain covered.

## Old

```lean
private theorem matrix_coefficient_pullback (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    {X Y : Scheme.{u}} (f : Y ⟶ X) {n t : ℕ}
    (a : Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) n ⟶
      Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) t)
    (i : Fin t) (j : Fin n) (y : Y) :
    integralMatrixPullbackFunctions ℓ E f a i j y =
      integralMatrixFunctions ℓ E X
        (chartComparison X (continuousIntegers ℓ E)) a i j (f y)
```

## New

```lean
theorem matrix_coefficient_pullback (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    {X Y : Scheme.{u}} (f : Y ⟶ X) {n t : ℕ}
    (a : Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) n ⟶
      Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) t)
    (i : Fin t) (j : Fin n) (y : Y) :
    integralMatrixPullbackFunctions ℓ E f a i j y =
      integralMatrixFunctions ℓ E X
        (chartComparison X (continuousIntegers ℓ E)) a i j (f y)
```

## Users

Every transitive importer from tools/downstream.py is listed, together with the new callers. The original helpers had no external users while private.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ContinuousConstructibleIntegralDenominators | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousConstructibleIntegralGluing | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousConstructibleIntegralImage | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousConstructibleIntegralModel | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousConstructibleIntegralSingle | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousConstructibleIntegralStratum | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousExchangeIntegralModel | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousFiniteEtaleLatticeDescent | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousFiniteFreeKernelModel | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousIntegralComplexTelescope | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousIntegralExchangeSquare | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousIntegralLocalization | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousIntegralLocalizationColimitTransport | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousIntegralLocalizationContinuity | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousIntegralLocalizationCounit | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousIntegralLocalizationHomology | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousIntegralLocalizationLegs | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousIntegralLocalizationMate | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousIntegralLocalizationModel | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousIntegralModuleTelescope | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousIntegralPushComparison | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousIntegralRegularTelescope | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousIntegralUnderivedPushComparison | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousLatticeIntersectionLocalModel | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalModel | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalization | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitData | B2 | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitModel | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousLisseStratifiedLattices | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.IntegralConstructibleKernels | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.IntegralConstructibleSequentialHom | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.IntegralConstructibleSerre | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.IntegralConstructibleSheafHom | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.IntegralFiniteExchangeComparison | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.IntegralLfpEventualFreeImage | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.IntegralLfpFiniteQuotientCharts | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.IntegralLfpHomContinuity | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.IntegralLfpLocalTorsionCharts | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.IntegralLfpLocallyFreeResolution | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.IntegralMatrixAnalyticCover | unclaimed | Imports and uses shared API; theorem signature unchanged |
| Sheaf.Paper.IntegralMatrixCoefficientTransport | E4 (new) | Imports and uses shared API; theorem signature unchanged |
| Sheaf.Paper.IntegralMatrixEntryProperties | unclaimed | Imports and uses shared API; theorem signature unchanged |
| Sheaf.Paper.IntegralMatrixFunctionsPullback | unclaimed | API exposed/generalized as above |
| Sheaf.Paper.IntegralMatrixKernelLocallyFree | unclaimed | Imports and uses shared API; theorem signature unchanged |
| Sheaf.Paper.IntegralMatrixPivotCover | unclaimed | Imports and uses shared API; theorem signature unchanged |
| Sheaf.Paper.IntegralMatrixPointwiseRank | E4 | Imports and uses shared API; theorem signature unchanged |
| Sheaf.Paper.IntegralMatrixZeroNeighborhood | unclaimed | Imports and uses shared API; theorem signature unchanged |
| Sheaf.Paper.IntegralReductionConservative | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.IntegralReductionConstructible | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.IntegralRegularRationalUnit | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.IntegralResidueExchange | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | No statement or definition changes; no adaptation |
| TargetsCheck | unclaimed | No statement or definition changes; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | No statement or definition changes; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | No statement or definition changes; no adaptation |

## Status

landed 20261016T093726-L-2050747 2026-10-16 (merge of deliver/E4/Sheaf.Paper.IntegralMatrixPointwiseRank)
