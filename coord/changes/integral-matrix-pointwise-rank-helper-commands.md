# AlgebraicGeometry.ProEtale.CondensedRing.integralMatrix_pointwise_rank

## Reason

The proof adds private geometric-evaluation helpers, extra universe names, namespace
opens and local instances for the explicit lifted normed field and geometric point.
The original theorem keeps exactly the same signature and visibility. All added helper
definitions and lemmas in this item are private, and all their proofs are complete.
The two original public imports stay public. Extra imports are proof-only.

The returned coordinate, cokernel-dimension and matrix-pullback copies have been
removed. The proof now imports and uses the corresponding APIs from their existing
modules, generalized or exposed in place as recorded in E4-reuse-*.md.
The new coefficient-transport module's existence theorem is fully proved; no hole
is added. No target statement or existing public mathematical statement changes.

## Old

```lean
theorem integralMatrix_pointwise_rank (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    (n t : ℕ) (X : Scheme.{u})
    (a : Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) n ⟶
      Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) t)
    (hC : ∃ V : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ k,
      Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} (V.f k)).obj
          (condensedRingObj (Profinite.continuousMapRingObj E) X))
        (((ProEtale.upperStar Ab.{u + 1} (V.f k)).mapMod _).obj
          ((Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X)).obj
            (cokernel a)))) :
    ∃ V : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ k (x y : V.X k),
      Matrix.rank (fun i j ↦ (integralMatrixPullbackFunctions ℓ E (V.f k) a i j x).val) =
        Matrix.rank (fun i j ↦ (integralMatrixPullbackFunctions ℓ E (V.f k) a i j y).val)
```

## New

```lean
theorem integralMatrix_pointwise_rank (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    (n t : ℕ) (X : Scheme.{u})
    (a : Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) n ⟶
      Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) t)
    (hC : ∃ V : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ k,
      Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} (V.f k)).obj
          (condensedRingObj (Profinite.continuousMapRingObj E) X))
        (((ProEtale.upperStar Ab.{u + 1} (V.f k)).mapMod _).obj
          ((Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X)).obj
            (cokernel a)))) :
    ∃ V : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ k (x y : V.X k),
      Matrix.rank (fun i j ↦ (integralMatrixPullbackFunctions ℓ E (V.f k) a i j x).val) =
        Matrix.rank (fun i j ↦ (integralMatrixPullbackFunctions ℓ E (V.f k) a i j y).val)
```

The private helper section declares universes for vector spaces and auxiliary
categories, opens the same standard category namespaces, and adds the local
`liftedNormedField` instance and the local field/algebraic-closure instances on the private `GeometricLift` record. These are scoped implementation commands; importers
receive the unchanged theorem signature.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralMatrixPointwiseRank | E4 | Proof replaced; signature unchanged |
| Sheaf.Paper.ContinuousConstructibleIntegralDenominators | unclaimed | No signature or definition changes; no adaptation |
| Sheaf.Paper.ContinuousConstructibleIntegralGluing | unclaimed | No signature or definition changes; no adaptation |
| Sheaf.Paper.ContinuousConstructibleIntegralImage | unclaimed | No signature or definition changes; no adaptation |
| Sheaf.Paper.ContinuousConstructibleIntegralModel | unclaimed | No signature or definition changes; no adaptation |
| Sheaf.Paper.ContinuousConstructibleIntegralSingle | unclaimed | No signature or definition changes; no adaptation |
| Sheaf.Paper.ContinuousConstructibleIntegralStratum | unclaimed | No signature or definition changes; no adaptation |
| Sheaf.Paper.ContinuousExchangeIntegralModel | unclaimed | No signature or definition changes; no adaptation |
| Sheaf.Paper.ContinuousIntegralComplexTelescope | unclaimed | No signature or definition changes; no adaptation |
| Sheaf.Paper.ContinuousIntegralExchangeSquare | unclaimed | No signature or definition changes; no adaptation |
| Sheaf.Paper.ContinuousIntegralLocalization | unclaimed | No signature or definition changes; no adaptation |
| Sheaf.Paper.ContinuousIntegralLocalizationColimitTransport | unclaimed | No signature or definition changes; no adaptation |
| Sheaf.Paper.ContinuousIntegralLocalizationContinuity | unclaimed | No signature or definition changes; no adaptation |
| Sheaf.Paper.ContinuousIntegralLocalizationHomology | unclaimed | No signature or definition changes; no adaptation |
| Sheaf.Paper.ContinuousIntegralLocalizationLegs | unclaimed | No signature or definition changes; no adaptation |
| Sheaf.Paper.ContinuousIntegralLocalizationMate | unclaimed | No signature or definition changes; no adaptation |
| Sheaf.Paper.ContinuousIntegralLocalizationModel | unclaimed | No signature or definition changes; no adaptation |
| Sheaf.Paper.ContinuousIntegralModuleTelescope | unclaimed | No signature or definition changes; no adaptation |
| Sheaf.Paper.ContinuousIntegralPushComparison | unclaimed | No signature or definition changes; no adaptation |
| Sheaf.Paper.ContinuousIntegralRegularTelescope | unclaimed | No signature or definition changes; no adaptation |
| Sheaf.Paper.IntegralConstructibleKernels | unclaimed | No signature or definition changes; no adaptation |
| Sheaf.Paper.IntegralConstructibleSequentialHom | unclaimed | No signature or definition changes; no adaptation |
| Sheaf.Paper.IntegralConstructibleSerre | unclaimed | No signature or definition changes; no adaptation |
| Sheaf.Paper.IntegralConstructibleSheafHom | unclaimed | No signature or definition changes; no adaptation |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | No signature or definition changes; no adaptation |
| Sheaf.Paper.IntegralFiniteExchangeComparison | unclaimed | No signature or definition changes; no adaptation |
| Sheaf.Paper.IntegralLfpEventualFreeImage | unclaimed | No signature or definition changes; no adaptation |
| Sheaf.Paper.IntegralLfpFiniteQuotientCharts | unclaimed | No signature or definition changes; no adaptation |
| Sheaf.Paper.IntegralLfpHomContinuity | unclaimed | No signature or definition changes; no adaptation |
| Sheaf.Paper.IntegralLfpLocalTorsionCharts | unclaimed | No signature or definition changes; no adaptation |
| Sheaf.Paper.IntegralLfpLocallyFreeResolution | unclaimed | No signature or definition changes; no adaptation |
| Sheaf.Paper.IntegralMatrixAnalyticCover | unclaimed | No signature or definition changes; no adaptation |
| Sheaf.Paper.IntegralMatrixEntryProperties | unclaimed | No signature or definition changes; no adaptation |
| Sheaf.Paper.IntegralMatrixPivotCover | unclaimed | No signature or definition changes; no adaptation |
| Sheaf.Paper.IntegralMatrixZeroNeighborhood | unclaimed | No signature or definition changes; no adaptation |
| Sheaf.Paper.IntegralReductionConservative | unclaimed | No signature or definition changes; no adaptation |
| Sheaf.Paper.IntegralReductionConstructible | unclaimed | No signature or definition changes; no adaptation |
| Sheaf.Paper.IntegralRegularRationalUnit | unclaimed | No signature or definition changes; no adaptation |
| Sheaf.Paper.IntegralResidueExchange | unclaimed | No signature or definition changes; no adaptation |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | No signature or definition changes; no adaptation |
| TargetsCheck | unclaimed | No signature or definition changes; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | No signature or definition changes; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | No signature or definition changes; no adaptation |

## Status

landed 20261016T093726-L-2050747 2026-10-16 (merge of deliver/E4/Sheaf.Paper.IntegralMatrixPointwiseRank)
