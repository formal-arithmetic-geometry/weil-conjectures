# AlgebraicGeometry.Etale.derivedTensor_isZero_homology_of_torAmplitudeGE

## Reason

Preflight requests a record for the added universe and namespace-opening commands.
They support private generic proof helpers. The public theorem has exactly its
original signature and visibility; no definition is changed or introduced. All
additional imports are proof-only. Module-system imports do not export local `open`
commands or universe declarations to consumers. This change therefore has no effect
on any downstream statement or target meaning, and forces no consumer adaptation.

## Old

```lean
universe u

open CategoryTheory CategoryTheory.Limits

theorem derivedTensor_isZero_homology_of_torAmplitudeGE
    (Λ : Type (u + 1)) [CommRing Λ] (T : Scheme.{u})
    (A B : DerivedCategoryModule Λ T) (a b : ℤ)
    (hA : DerivedCategory.hasTorAmplitudeGE Λ T a A)
    (hB : ∀ (j : ℤ), j < b →
      IsZero ((_root_.DerivedCategory.homologyFunctor
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) j).obj B))
    (i : ℤ) (hi : i < a + b) :
    IsZero ((_root_.DerivedCategory.homologyFunctor
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) i).obj
      (((derivedTensor (ModuleCat.{u + 1} Λ) T).obj A).obj B))
```

## New

```lean
universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory

theorem derivedTensor_isZero_homology_of_torAmplitudeGE
    (Λ : Type (u + 1)) [CommRing Λ] (T : Scheme.{u})
    (A B : DerivedCategoryModule Λ T) (a b : ℤ)
    (hA : DerivedCategory.hasTorAmplitudeGE Λ T a A)
    (hB : ∀ (j : ℤ), j < b →
      IsZero ((_root_.DerivedCategory.homologyFunctor
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) j).obj B))
    (i : ℤ) (hi : i < a + b) :
    IsZero ((_root_.DerivedCategory.homologyFunctor
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) i).obj
      (((derivedTensor (ModuleCat.{u + 1} Λ) T).obj A).obj B))
```

The sole public declaration now has a complete proof. Four proved private helpers
handle exact filtered colimits, the truncation filtration, the generic tensor bound
and its etale specialization. The public statement, including all universe levels,
was checked textually against the current shared source before delivery.

## Users

Generated from `tools/downstream.py Sheaf.Paper.KunnethDerivedTensorTEst --uses
AlgebraicGeometry.Etale.derivedTensor_isZero_homology_of_torAmplitudeGE` against the
current shared sources. Its textual declaration search finds only the item's own
declaration; the full transitive import closure has 221 modules, listed below.
Every listed module retains its exact statement because the public signature and
definitions are unchanged. No consumer file is adapted or delivered. Holder labels
are snapshots of the shared claim records.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.Paper.KunnethDerivedTensorTEst` | V2 | unchanged signatures; no adaptation |
| `Sheaf.AlgebraicGeometry.ProjectionComparisonEtaleOrigin` | A2 | unchanged signatures; no adaptation |
| `Sheaf.DeligneLaumon.GenericDualityModel` | unclaimed | unchanged signatures; no adaptation |
| `Sheaf.DeligneLaumon.QbarCurveDuality` | unclaimed | unchanged signatures; no adaptation |
| `Sheaf.DeligneLaumon.Reduction.AffineCurveUpper` | unclaimed | unchanged signatures; no adaptation |
| `Sheaf.DeligneLaumon.Reduction.Composition` | unclaimed | unchanged signatures; no adaptation |
| `Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift` | unclaimed | unchanged signatures; no adaptation |
| `Sheaf.Paper.AdicPurityExceptionalReduction` | unclaimed | unchanged signatures; no adaptation |
| `Sheaf.Paper.AdicPurityFiniteTensor` | W8 | unchanged signatures; no adaptation |
| `Sheaf.Paper.AdicPurityObjects` | unclaimed | unchanged signatures; no adaptation |
| `Sheaf.Paper.AdicPurityRootComparisons` | X5 | unchanged signatures; no adaptation |
| `Sheaf.Paper.AdicPuritySourceReduction` | X6 | unchanged signatures; no adaptation |
| `Sheaf.Paper.AdicPurityTwistReduction` | X8 | unchanged signatures; no adaptation |
| `Sheaf.Paper.AdicSmoothDualizingComplexes` | unclaimed | unchanged signatures; no adaptation |
| `Sheaf.Paper.ArithmeticRoots` | unclaimed | unchanged signatures; no adaptation |
| `Sheaf.Paper.ChernFlagFormula` | G4 | unchanged signatures; no adaptation |
| `Sheaf.Paper.CohomologicalSmoothEtaleLocality` | unclaimed | unchanged signatures; no adaptation |
| `Sheaf.Paper.CohomologicalSmoothnessTheorem` | unclaimed | unchanged signatures; no adaptation |
| `Sheaf.Paper.CommonStageConstituentNonexceptional` | P2 | unchanged signatures; no adaptation |
| `Sheaf.Paper.CommonStageFourierWeightUpper` | unclaimed | unchanged signatures; no adaptation |
| `Sheaf.Paper.CompletedStalkFrobeniusReduction` | A4 | unchanged signatures; no adaptation |
| `Sheaf.Paper.CurveIntermediateExtension` | unclaimed | unchanged signatures; no adaptation |
| `Sheaf.Paper.CurveMiddleExtensionUpper` | unclaimed | unchanged signatures; no adaptation |
| `Sheaf.Paper.DualizingObjectPurity` | unclaimed | unchanged signatures; no adaptation |
| `Sheaf.Paper.EtaleRhoMonoidalMate` | unclaimed | unchanged signatures; no adaptation |
| `Sheaf.Paper.ExtensionByZeroPunctual` | unclaimed | unchanged signatures; no adaptation |
| `Sheaf.Paper.FiniteCoefficientSmoothPurity` | unclaimed | unchanged signatures; no adaptation |
| `Sheaf.Paper.FiniteEtaleLisseWeilImage` | H7 | unchanged signatures; no adaptation |
| `Sheaf.Paper.FiniteReductionAffineOrientation` | T6 | unchanged signatures; no adaptation |
| `Sheaf.Paper.FiniteReductionChartCalculus` | S7 | unchanged signatures; no adaptation |
| `Sheaf.Paper.FiniteReductionComparisons` | T7 | unchanged signatures; no adaptation |
| `Sheaf.Paper.FiniteReductionOfPurity` | unclaimed | unchanged signatures; no adaptation |
| `Sheaf.Paper.FiniteReductionRootCharts` | D8 | unchanged signatures; no adaptation |
| `Sheaf.Paper.FiniteSmoothPullbackExchange` | V6 | unchanged signatures; no adaptation |
| `Sheaf.Paper.FiniteTorStability` | unclaimed | unchanged signatures; no adaptation |
| `Sheaf.Paper.FiniteUniversalSmoothTrace` | unclaimed | unchanged signatures; no adaptation |
| `Sheaf.Paper.FixedStalkIdentificationReduction` | W4 | unchanged signatures; no adaptation |
| `Sheaf.Paper.FlagLocalComparison` | unclaimed | unchanged signatures; no adaptation |
| `Sheaf.Paper.FlagPullbackInjective` | unclaimed | unchanged signatures; no adaptation |
| `Sheaf.Paper.FourierTraceFormula` | unclaimed | unchanged signatures; no adaptation |
| `Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology` | unclaimed | unchanged signatures; no adaptation |
| `Sheaf.Paper.LocalizedFlagProduct` | unclaimed | unchanged signatures; no adaptation |
| `Sheaf.Paper.LocalizedTopChern` | E5 | unchanged signatures; no adaptation |
| `Sheaf.Paper.ProjectiveBundleFormula` | unclaimed | unchanged signatures; no adaptation |
| `Sheaf.Paper.PurAdicReconstruction` | H8 | unchanged signatures; no adaptation |
| `Sheaf.Paper.PurityChernClasses` | unclaimed | unchanged signatures; no adaptation |
| `Sheaf.Paper.PurityCompositionCoherence` | unclaimed | unchanged signatures; no adaptation |
| `Sheaf.Paper.PurityDiagonalBaseChangeCompared` | R3 | unchanged signatures; no adaptation |
| `Sheaf.Paper.PurityDiagonalDualizingObject` | G3 | unchanged signatures; no adaptation |
| `Sheaf.Paper.PurityDiagonalSectionPasting` | unclaimed | unchanged signatures; no adaptation |
| `Sheaf.Paper.PurityDncComparisons` | G3 | unchanged signatures; no adaptation |
| `Sheaf.Paper.PurityDncFamilyIntrinsic` | unclaimed | unchanged signatures; no adaptation |
| `Sheaf.Paper.PurityDncInvariance` | unclaimed | unchanged signatures; no adaptation |
| `Sheaf.Paper.PuritySectionInvariantIntrinsic` | K6 | unchanged signatures; no adaptation |
| `Sheaf.Paper.QbarMiddleTStructure` | unclaimed | unchanged signatures; no adaptation |
| `Sheaf.Paper.QbarPerverseSubcategories` | unclaimed | unchanged signatures; no adaptation |
| `Sheaf.Paper.QbarPerverseSupportCondition` | unclaimed | unchanged signatures; no adaptation |
| `Sheaf.Paper.QuasiFiniteCompactSupportWeights` | K7 | unchanged signatures; no adaptation |
| `Sheaf.Paper.RationalPurityPresentation` | unclaimed | unchanged signatures; no adaptation |
| `Sheaf.Paper.RationalScalarTransposeCompatibility` | K8 | unchanged signatures; no adaptation |
| `Sheaf.Paper.RationalSmoothPurityCanonical` | W5 | unchanged signatures; no adaptation |
| `Sheaf.Paper.RationalWeilPurityNaturalityMate` | unclaimed | unchanged signatures; no adaptation |
| `Sheaf.Paper.RegularImmersionPurityComparison` | unclaimed | unchanged signatures; no adaptation |
| `Sheaf.Paper.SfBidualityClass` | C6 | unchanged signatures; no adaptation |
| `Sheaf.Paper.SmoothProperPurityHypotheses` | unclaimed | unchanged signatures; no adaptation |
| `Sheaf.Paper.SmoothPullbackSupportDimension` | unclaimed | unchanged signatures; no adaptation |
| `Sheaf.Paper.SmoothPurityMap` | R2 | unchanged signatures; no adaptation |
| `Sheaf.Paper.SmoothTrace` | unclaimed | unchanged signatures; no adaptation |
| `Sheaf.Paper.SupportedProjectionSplitting` | unclaimed | unchanged signatures; no adaptation |
| `Sheaf.Paper.TateTwistSupportCondition` | unclaimed | unchanged signatures; no adaptation |
| `Sheaf.Paper.TraceFormulaTopologicalInvariance` | unclaimed | unchanged signatures; no adaptation |
| `Sheaf.Paper.TwistFrobeniusScalar` | G4 | unchanged signatures; no adaptation |
| `Sheaf.Paper.VectorBundleThomClass` | unclaimed | unchanged signatures; no adaptation |
| `Sheaf.Paper.WeilCohomologyScalarExtensionQlbar` | unclaimed | unchanged signatures; no adaptation |
| `Sheaf.Paper.WeilFourierInversion` | J6 | unchanged signatures; no adaptation |
| `Sheaf.Paper.WeilFourierPlancherel` | unclaimed | unchanged signatures; no adaptation |
| `Sheaf.Paper.WeilOne` | unclaimed | unchanged signatures; no adaptation |
| `Sheaf.Paper.ZlShriekComposition` | unclaimed | unchanged signatures; no adaptation |
| `Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility` | unclaimed | unchanged signatures; no adaptation |
| `Sheaf.SecSmoothPurity.FiniteGeneralRing` | D6 | unchanged signatures; no adaptation |
| `Sheaf.SecSmoothPurity.PurityDncCoefficientTransport` | K9 | unchanged signatures; no adaptation |
| `Sheaf.SecSmoothPurity.RationalPurityTraceCoherence` | unclaimed | unchanged signatures; no adaptation |
| `Sheaf.SecSmoothPurity.ReductionCompatibilities` | E6 | unchanged signatures; no adaptation |
| `Sheaf.SecSmoothPurity.SmoothPurityNaturality` | unclaimed | unchanged signatures; no adaptation |
| `Sheaf.SixFunctors.ArbitraryFieldVerdier` | unclaimed | unchanged signatures; no adaptation |
| `Sheaf.SixFunctors.CoefDualFormulaScalarTranspose` | unclaimed | unchanged signatures; no adaptation |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtension` | A9 | unchanged signatures; no adaptation |
| `Sheaf.SixFunctors.CoefQbarVerdier` | R5 | unchanged signatures; no adaptation |
| `Sheaf.SixFunctors.CoefTowerNaturalCurrying` | F2 | unchanged signatures; no adaptation |
| `Sheaf.SixFunctors.FiniteExceptional` | unclaimed | unchanged signatures; no adaptation |
| `Sheaf.SixFunctors.FiniteMappingAdjunction` | J7 | unchanged signatures; no adaptation |
| `Sheaf.SixFunctors.IntegralDualizing` | unclaimed | unchanged signatures; no adaptation |
| `Sheaf.SixFunctors.IntegralVerdier` | V2 | unchanged signatures; no adaptation |
| `Sheaf.SixFunctors.QbarDualRecollement` | unclaimed | unchanged signatures; no adaptation |
| `Sheaf.SixFunctors.RationalOperations` | unclaimed | unchanged signatures; no adaptation |
| `Sheaf.SixFunctors.RationalRetractEvaluation` | A4 | unchanged signatures; no adaptation |
| `Sheaf.SixFunctors.RationalVerdier` | V4 | unchanged signatures; no adaptation |
| `Sheaf.ZetaWeil.WeightPurityRoots` | unclaimed | unchanged signatures; no adaptation |
| `TargetsCheck` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.DeligneLaumon.AffineLine.Concentration` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.DeligneLaumon.AffineLine.DegreeOne` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.DeligneLaumon.AffineLine.Exactness` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierWeight` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.DeligneLaumon.AffineLine.LocalDuality` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.DeligneLaumon.AffineLine.Perverse` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.DeligneLaumon.AffineLine.Purity` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.DeligneLaumon.AffineLine.RealPushforward` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.DeligneLaumon.AffineLine.Upper` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.DeligneLaumon.AffineLine.UpperReduction` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.DeligneLaumon.Reduction.AffineCurve` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.DeligneLaumon.Reduction.CompactSupport` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.DeligneLaumon.Reduction.DirectImage` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.DeligneLaumon.Reduction.FibreCohomology` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.DeligneLaumon.Reduction.FiniteMap` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.DeligneLaumon.Reduction.FormalSteps` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.DeligneLaumon.Reduction.MixedStalk` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.DeligneLaumon.Reduction.OpenLine` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.DeligneLaumon.Reduction.RealCurve` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.DeligneLaumon.Reduction.RealSheaves` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Adic` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Rational` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.SixFunctors.Adic.Reduction` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.SixFunctors.Etale.Derived.ClosedUpperShriekCoproducts` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.SixFunctors.Etale.Derived.CompactConstructible` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.SixFunctors.Etale.Derived.CompactSupportIntegral` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.SixFunctors.Etale.Derived.ExcisionComparison` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactLocalizing` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekLocalizing` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.Statement` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.WeilSheaf.AffineLineCohomology` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.WeilSheaf.CohomologicalRange` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.WeilSheaf.CohomologicalRangeAffine` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.WeilSheaf.Curve` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.WeilSheaf.CurveEndpoints` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.WeilSheaf.CurveTopCohomology` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.WeilSheaf.EulerProduct` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.WeilSheaf.FourierInversion` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.WeilSheaf.FourierInversion.Composite` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.WeilSheaf.FourierInversion.Delta` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.WeilSheaf.FourierInversion.OtherSections` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.WeilSheaf.FourierInversion.Vanishing` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.WeilSheaf.FourierPlancherel` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.WeilSheaf.FourierStalk` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.WeilSheaf.FourierTrace` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.WeilSheaf.GrothendieckLefschetz` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.WeilSheaf.LFunction` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.WeilSheaf.LissePoincarePairing` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.WeilSheaf.LocalizationRational` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.WeilSheaf.LowerShriekFunctoriality` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.WeilSheaf.LowerShriekOperations` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.WeilSheaf.LowerShriekPackage` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.WeilSheaf.OpenClosedTriangle` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.WeilSheaf.PoincareDualityLisse` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.WeilSheaf.RealPurity` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.WeilSheaf.TraceIsomorphism` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.WeilSheaf.VerdierDual` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.WeilSheaf.VerdierDualFinite` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.WeilSheaf.VerdierDualLocalization` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.ZetaFunction.BettiSymmetry` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.ZetaFunction.CohomologicalFamily` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.ZetaFunction.DualityReciprocity` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.ZetaFunction.Examples` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.ZetaFunction.ExamplesCohomology` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.ZetaFunction.FinalTheorems` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.ZetaFunction.HasseWeil` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.ZetaFunction.IntegralFactors` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.ZetaFunction.IntegralFrobeniusFactors` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.ZetaFunction.LissePurity` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.ZetaFunction.Rationality` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.ZetaFunction.RealizationIndependence` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.ZetaFunction.RelativePurity` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.ZetaFunction.SmoothProper` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.ZetaFunction.TraceFormula` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.ZetaFunction.WeightSeparation` | unclaimed | unchanged signatures; no adaptation |
| `WeilConjectures.ZetaFunction.Weights` | unclaimed | unchanged signatures; no adaptation |

## Status

landed 20261019T192845-L-1876737 2026-10-19 (merge of deliver/V2/Sheaf.Paper.KunnethDerivedTensorTEst)
