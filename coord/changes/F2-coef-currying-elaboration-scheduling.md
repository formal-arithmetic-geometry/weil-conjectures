# Sheaf.SixFunctors.CoefTowerNaturalCurrying elaboration scheduling

## Reason

Restore normal asynchronous elaboration of independent declarations. The full
source compiled in 37.3 seconds after this change. Earlier sequential checks
varied between successful compiles and 60-second timeouts. This option changes
elaboration scheduling only; every declaration type, body, visibility and import
is unchanged. No timeout or heartbeat limit is raised; nothing is split.
The other Lean edit marks the trace statement STATEMENT-DISPUTED.

## Old

```lean
set_option Elab.async false
```

## New

```lean
set_option Elab.async true
```

## Users

All transitive library consumers are listed below. The local scheduling option
is not exported. No mathematical definition or target statement changes, and
no consumer adaptation is required. External references to finiteArrow occur
only in Sheaf.SixFunctors.FiniteAdjunctionTransition; its signature and body
remain identical. There is no external reference to coefCurryingPointEvaluation.

| module | group holding it | effect |
|---|---|---|
| Sheaf.DeligneLaumon.GenericDualityModel | unclaimed | Existing types and bodies unchanged; no adaptation. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Existing types and bodies unchanged; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Existing types and bodies unchanged; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | Existing types and bodies unchanged; no adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Existing types and bodies unchanged; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Existing types and bodies unchanged; no adaptation. |
| Sheaf.Paper.ChernFlagFormula | G4 | Existing types and bodies unchanged; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Existing types and bodies unchanged; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | P2 | Existing types and bodies unchanged; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Existing types and bodies unchanged; no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | A4 | Existing types and bodies unchanged; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Existing types and bodies unchanged; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Existing types and bodies unchanged; no adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Existing types and bodies unchanged; no adaptation. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | H7 | Existing types and bodies unchanged; no adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Existing types and bodies unchanged; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | W4 | Existing types and bodies unchanged; no adaptation. |
| Sheaf.Paper.FlagLocalComparison | unclaimed | Existing types and bodies unchanged; no adaptation. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Existing types and bodies unchanged; no adaptation. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Existing types and bodies unchanged; no adaptation. |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | unclaimed | Existing types and bodies unchanged; no adaptation. |
| Sheaf.Paper.GlobalVerdierDuality | unclaimed | Existing types and bodies unchanged; no adaptation. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | Existing types and bodies unchanged; no adaptation. |
| Sheaf.Paper.LocalizedTopChern | E5 | Existing types and bodies unchanged; no adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | Existing types and bodies unchanged; no adaptation. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Existing types and bodies unchanged; no adaptation. |
| Sheaf.Paper.QbarMiddleTStructure | unclaimed | Existing types and bodies unchanged; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Existing types and bodies unchanged; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Existing types and bodies unchanged; no adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | K7 | Existing types and bodies unchanged; no adaptation. |
| Sheaf.Paper.RationalPurityPresentation | unclaimed | Existing types and bodies unchanged; no adaptation. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | K8 | Existing types and bodies unchanged; no adaptation. |
| Sheaf.Paper.RationalSmoothPurityCanonical | W5 | Existing types and bodies unchanged; no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Existing types and bodies unchanged; no adaptation. |
| Sheaf.Paper.SfBidualityClass | C6 | Existing types and bodies unchanged; no adaptation. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | Existing types and bodies unchanged; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Existing types and bodies unchanged; no adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Existing types and bodies unchanged; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Existing types and bodies unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Existing types and bodies unchanged; no adaptation. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | Existing types and bodies unchanged; no adaptation. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | Existing types and bodies unchanged; no adaptation. |
| Sheaf.Paper.WeilFourierInversion | J6 | Existing types and bodies unchanged; no adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Existing types and bodies unchanged; no adaptation. |
| Sheaf.Paper.WeilOne | unclaimed | Existing types and bodies unchanged; no adaptation. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Existing types and bodies unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | unclaimed | Existing types and bodies unchanged; no adaptation. |
| Sheaf.SixFunctors.ArbitraryFieldVerdier | unclaimed | Existing types and bodies unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Existing types and bodies unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | A9 | Existing types and bodies unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | R5 | Existing types and bodies unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | unclaimed | Existing types and bodies unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | H6 | Existing types and bodies unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteExceptional | unclaimed | Existing types and bodies unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | G8 | Existing types and bodies unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | V2 | Existing types and bodies unchanged; no adaptation. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | R6 | Existing types and bodies unchanged; no adaptation. |
| Sheaf.SixFunctors.QbarDualRecollement | unclaimed | Existing types and bodies unchanged; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Existing types and bodies unchanged; no adaptation. |
| Sheaf.SixFunctors.RationalRetractEvaluation | A4 | Existing types and bodies unchanged; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | V4 | Existing types and bodies unchanged; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Adic.Reduction | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ClosedUpperShriekCoproducts | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactConstructible | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactSupportIntegral | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ExcisionComparison | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactLocalizing | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekLocalizing | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.Statement | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRange | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.CurveTopCohomology | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierPlancherel | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierStalk | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierTrace | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LissePoincarePairing | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekPackage | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.OpenClosedTriangle | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.PoincareDualityLisse | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDual | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Existing types and bodies unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Existing types and bodies unchanged; no adaptation. |

## Status

landed 20261019T231142-L-555123 2026-10-19 (merge of deliver/F2/Sheaf.SixFunctors.CoefTowerNaturalCurrying)
