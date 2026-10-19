# AlgebraicGeometry.ProEtale.openDirectImage_classical_amplitude

## Reason

Remove two unused public imports while proving the unchanged amplitude theorem. The proof uses the original canonical site comparison and the existing bounded-below derived API. No declaration, definition, or statement changes.

## Old

```lean
public import Sheaf.AlgebraicGeometry.ProEtaleSmallModelComparison
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
```

## New

These two public imports are removed. All remaining original public imports and the theorem signature are unchanged. New imports are proof-only.

## Users

Both direct importers import this module only for proofs. Their existing declarations are unchanged; neither uses declarations from the removed modules through this import. Their public interfaces therefore propagate no export change to their own consumers. The table includes the transitive source-import closure; no consumer needs adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.DeligneLaumon.GenericDualityModel | unclaimed | Indirect importer; no public export change reaches this module. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Indirect importer; no public export change reaches this module. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Indirect importer; no public export change reaches this module. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | Indirect importer; no public export change reaches this module. |
| Sheaf.Paper.AdicExceptionalProjection | unclaimed | Indirect importer; no public export change reaches this module. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Indirect importer; no public export change reaches this module. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Indirect importer; no public export change reaches this module. |
| Sheaf.Paper.ChernFlagFormula | unclaimed | Indirect importer; no public export change reaches this module. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Indirect importer; no public export change reaches this module. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | P2 | Indirect importer; no public export change reaches this module. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Indirect importer; no public export change reaches this module. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | A4 | Indirect importer; no public export change reaches this module. |
| Sheaf.Paper.ConstructibleFiniteTorAdjunctions | C6 | Indirect importer; no public export change reaches this module. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Indirect importer; no public export change reaches this module. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Indirect importer; no public export change reaches this module. |
| Sheaf.Paper.DetThmSfCtfStabilityInternalHom | J7 | Indirect importer; no public export change reaches this module. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Indirect importer; no public export change reaches this module. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | H7 | Indirect importer; no public export change reaches this module. |
| Sheaf.Paper.FiniteExceptionalSystemAdjunction | unclaimed | Direct proof-only importer; no removed declaration used; no adaptation. |
| Sheaf.Paper.FiniteRegularReductionDualizing | unclaimed | Indirect importer; no public export change reaches this module. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Indirect importer; no public export change reaches this module. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Indirect importer; no public export change reaches this module. |
| Sheaf.Paper.FixedStalkIdentificationReduction | W4 | Indirect importer; no public export change reaches this module. |
| Sheaf.Paper.FlagLocalComparison | unclaimed | Indirect importer; no public export change reaches this module. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Indirect importer; no public export change reaches this module. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Indirect importer; no public export change reaches this module. |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | unclaimed | Indirect importer; no public export change reaches this module. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | Indirect importer; no public export change reaches this module. |
| Sheaf.Paper.LocalizedTopChern | unclaimed | Indirect importer; no public export change reaches this module. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | Indirect importer; no public export change reaches this module. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Indirect importer; no public export change reaches this module. |
| Sheaf.Paper.QbarMiddleTStructure | unclaimed | Indirect importer; no public export change reaches this module. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Indirect importer; no public export change reaches this module. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Indirect importer; no public export change reaches this module. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | K7 | Indirect importer; no public export change reaches this module. |
| Sheaf.Paper.RationalPurityPresentation | unclaimed | Indirect importer; no public export change reaches this module. |
| Sheaf.Paper.RationalSmoothPurityCanonical | W5 | Indirect importer; no public export change reaches this module. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Indirect importer; no public export change reaches this module. |
| Sheaf.Paper.SfBidualityClass | C6 | Indirect importer; no public export change reaches this module. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | Indirect importer; no public export change reaches this module. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Indirect importer; no public export change reaches this module. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Indirect importer; no public export change reaches this module. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Indirect importer; no public export change reaches this module. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Indirect importer; no public export change reaches this module. |
| Sheaf.Paper.VectorBundleThomClass | X2 | Indirect importer; no public export change reaches this module. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | Indirect importer; no public export change reaches this module. |
| Sheaf.Paper.WeilFourierInversion | J6 | Indirect importer; no public export change reaches this module. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Indirect importer; no public export change reaches this module. |
| Sheaf.Paper.WeilOne | unclaimed | Indirect importer; no public export change reaches this module. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Indirect importer; no public export change reaches this module. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | D6 | Indirect importer; no public export change reaches this module. |
| Sheaf.SecSmoothPurity.MixedBaseChange | Z8 | Indirect importer; no public export change reaches this module. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | K9 | Indirect importer; no public export change reaches this module. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | unclaimed | Indirect importer; no public export change reaches this module. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | E6 | Indirect importer; no public export change reaches this module. |
| Sheaf.SixFunctors.ArbitraryFieldVerdier | unclaimed | Indirect importer; no public export change reaches this module. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Indirect importer; no public export change reaches this module. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | A9 | Indirect importer; no public export change reaches this module. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | Indirect importer; no public export change reaches this module. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | F2 | Indirect importer; no public export change reaches this module. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | J6 | Direct proof-only importer; no removed declaration used; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | J7 | Indirect importer; no public export change reaches this module. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Indirect importer; no public export change reaches this module. |
| Sheaf.SixFunctors.IntegralVerdier | V2 | Indirect importer; no public export change reaches this module. |
| Sheaf.SixFunctors.QbarDualRecollement | unclaimed | Indirect importer; no public export change reaches this module. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Indirect importer; no public export change reaches this module. |
| Sheaf.SixFunctors.RationalVerdier | V4 | Indirect importer; no public export change reaches this module. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Indirect importer; no public export change reaches this module. |
| TargetsCheck | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.SixFunctors.Adic.Reduction | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.SixFunctors.Etale.Derived.ClosedUpperShriekCoproducts | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactConstructible | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactSupportIntegral | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.SixFunctors.Etale.Derived.ExcisionComparison | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactLocalizing | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekLocalizing | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.Statement | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.WeilSheaf.CohomologicalRange | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.WeilSheaf.FourierPlancherel | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.WeilSheaf.FourierStalk | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.WeilSheaf.FourierTrace | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.WeilSheaf.LowerShriekPackage | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.WeilSheaf.OpenClosedTriangle | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.WeilSheaf.VerdierDual | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Indirect importer; no public export change reaches this module. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Indirect importer; no public export change reaches this module. |

## Status

landed 20261019T154025-L-3029090 2026-10-19 (merge of deliver/T6/Sheaf.AlgebraicGeometry.OpenDirectImageClassicalAmplitude)
