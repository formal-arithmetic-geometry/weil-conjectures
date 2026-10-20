# Sheaf.SixFunctors.CoefTowerEvaluationPairing file warning option

## Reason

Repair returned head ab1c5a094. The landing census interpreted the `sorry` component
of the warning option name as an unattributed proof hole at line 73. Remove the
unnecessary file-level warning suppression. This changes only warning behavior
while elaborating this file; Lean does not export option settings to its importers.
No mathematical statement, definition, universe, visibility or public import changes.
The five auxiliary proofs of the returned delivery are retained.

## Old

```lean
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.sorry false
set_option synthInstance.maxSize 4096
```

## New

```lean
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
```

## Users

Computed with `tools/downstream.py Sheaf.SixFunctors.CoefTowerEvaluationPairing`.
All consumers have identical mathematical interfaces. Importing modules have their
own option context, so none requires adaptation. The main theorem retains its
original statement and named proof hole; no target statement or meaning changes.

| module | group holding it | effect |
|---|---|---|
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | J1 | Same signatures, definitions and public imports; no consumer adaptation. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| Sheaf.Paper.ChernFlagFormula | G4 | Same signatures, definitions and public imports; no consumer adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | A4 | Same signatures, definitions and public imports; no consumer adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| Sheaf.Paper.FiniteDncNormalizationReduction | Q1 | Same signatures, definitions and public imports; no consumer adaptation. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | H7 | Same signatures, definitions and public imports; no consumer adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | W4 | Same signatures, definitions and public imports; no consumer adaptation. |
| Sheaf.Paper.FlagLocalComparison | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| Sheaf.Paper.GlobalVerdierDuality | R5 | Same signatures, definitions and public imports; no consumer adaptation. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| Sheaf.Paper.LocalizedTopChern | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | K7 | Same signatures, definitions and public imports; no consumer adaptation. |
| Sheaf.Paper.RationalPurityPresentation | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | K8 | Same signatures, definitions and public imports; no consumer adaptation. |
| Sheaf.Paper.RationalSmoothPurityCanonical | W5 | Same signatures, definitions and public imports; no consumer adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| Sheaf.Paper.WeilFourierInversion | J6 | Same signatures, definitions and public imports; no consumer adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | R5 | Same signatures, definitions and public imports; no consumer adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | T8 | Same signatures, definitions and public imports; no consumer adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | H6 | Same signatures, definitions and public imports; no consumer adaptation. |
| Sheaf.SixFunctors.FiniteExceptional | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | G8 | Same signatures, definitions and public imports; no consumer adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | V2 | Same signatures, definitions and public imports; no consumer adaptation. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | R6 | Same signatures, definitions and public imports; no consumer adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| Sheaf.SixFunctors.RationalRetractEvaluation | A4 | Same signatures, definitions and public imports; no consumer adaptation. |
| Sheaf.SixFunctors.RationalVerdier | V4 | Same signatures, definitions and public imports; no consumer adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| TargetsCheck | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.SixFunctors.Adic.Reduction | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ClosedUpperShriekCoproducts | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactConstructible | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactSupportIntegral | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ExcisionComparison | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactLocalizing | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekLocalizing | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.Statement | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRange | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.WeilSheaf.CurveTopCohomology | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.WeilSheaf.FourierPlancherel | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.WeilSheaf.FourierStalk | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.WeilSheaf.FourierTrace | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.WeilSheaf.LissePoincarePairing | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekPackage | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.WeilSheaf.OpenClosedTriangle | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.WeilSheaf.PoincareDualityLisse | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.WeilSheaf.VerdierDual | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Same signatures, definitions and public imports; no consumer adaptation. |

## Status

landed 20261020T051410-L-1667439 2026-10-20 (merge of deliver/J1/Sheaf.SixFunctors.CoefTowerEvaluationPairing)
