# AlgebraicGeometry.proEtale_finite_constant_sections

## Reason

Repair returned delivery `baf422ce8a`. The landing source-hole scanner interpreted
`set_option warn.sorry false` at line 32, offset 1083 as an unattributed hole.
Remove that unnecessary file-local warning option. The fully proved theorem and
all five private helpers contain no proof holes. This removal changes no Lean
declaration, type, definition, import visibility, notation or instance.

The preflight classifies any removal of a top-level option command as an
interface change and requests this record. The option only controlled warning
emission while elaborating this module. It is not an exported definition and
cannot change the mathematical meaning of any target or consumer.

## Old

```lean
set_option autoImplicit false
set_option warn.sorry false
```

## New

```lean
set_option autoImplicit false
```

The signature of `AlgebraicGeometry.proEtale_finite_constant_sections` remains
byte-for-byte unchanged. The other delivery changes complete its original proof
from Mathlib and update the node proof plan, as described in report.md.

## Users

`tools/downstream.py Sheaf.SecSmoothPurity.ProEtaleFiniteConstantSections --uses
AlgebraicGeometry.proEtale_finite_constant_sections` reports 207 downstream
modules, listed below. Only the item's own declaration mentions the theorem;
the direct importer is
`Sheaf.AlgebraicGeometry.ProEtaleSupportedConstantPresentation`. No consumer
requires adaptation: removing a file-local warning option does not affect any
imported type or definition. No target statement changes or reopens semantic
review. Holders below are a snapshot at preparation of this record.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.SecSmoothPurity.ProEtaleFiniteConstantSections` | unclaimed | Proof completed; unnecessary local warning option removed. |
| `Sheaf.AlgebraicGeometry.ProEtaleSupportedConstantPresentation` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.DeligneLaumon.Reduction.AffineCurveUpper` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.DeligneLaumon.Reduction.Composition` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.AdicPurityExceptionalReduction` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.AdicPurityFiniteTensor` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.AdicPurityObjects` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.AdicPurityRootComparisons` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.AdicPuritySourceReduction` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.AdicPurityTwistReduction` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.AdicSmoothDualizingComplexes` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.AffineLineOrdinaryInvariance` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.ArithmeticRoots` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.CartierClassAgreement` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.ChernFlagFormula` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.ClosedSupportedCupVanishing` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.CohomologicalSmoothnessTheorem` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.CommonStageConstituentNonexceptional` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.CommonStageFourierWeightUpper` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.CompactProductProperSupportCompatibility` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.CompactProductProperSupportLaws` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.CompactProductRealizationCoreLaws` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.CompactProductRealizationLaws` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.CompactProductTwistLaws` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.CompletionSupportedConstantComparison` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.CurveIntermediateExtension` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.CurveMiddleExtensionUpper` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.DualizingObjectPurity` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.ExtensionByZeroPunctual` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.FiniteCoefficientSmoothPurity` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.FiniteEtaleLisseWeilImage` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.FiniteReductionAffineOrientation` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.FiniteReductionChartCalculus` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.FiniteReductionComparisons` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.FiniteReductionOfPurity` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.FiniteReductionRootCharts` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.FiniteSmoothPullbackExchange` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.FlagPullbackInjective` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.FourierTraceFormula` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.LocalizedFlagProduct` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.LocalizedTopChern` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.ProjectiveBundleFormula` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.PurAdicReconstruction` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.PurityAffineLineOrientation` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.PurityAffineLineOrientationUniqueness` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.PurityChernClasses` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.PurityCompositionCoherence` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.PurityDiagonalBaseChangeCompared` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.PurityDiagonalDualizingObject` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.PurityDiagonalSectionPasting` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.PurityDivisorClass` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.PurityDncComparisons` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.PurityDncFamilyIntrinsic` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.PurityDncInvariance` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.PurityExteriorProductFrame` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.PurityFrameClass` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.PurityFrameIndependence` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.PurityFramePrincipalBoundary` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.PuritySectionInvariantIntrinsic` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.PurityTwistCancellation` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.QuasiFiniteCompactSupportWeights` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.RationalPurityPresentation` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.RationalSmoothPurityCanonical` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.RationalWeilPurityNaturalityMate` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.RegularImmersionCancellation` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.RegularImmersionClassData` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.RegularImmersionExteriorClass` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.RegularImmersionPurity` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.RegularImmersionPurityComparison` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.RegularImmersionSignedEvaluation` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.RelativeSupportBottomDescent` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.RelativeSupportCoordinateModel` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.SmoothProperPurityHypotheses` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.SmoothPurityMap` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.SmoothTrace` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.SupportedAffineLineHomotopy` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.SupportedClassGeometry` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.SupportedClassSiteComparison` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.SupportedCohomologyHom` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.SupportedCup` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.SupportedCupFunctoriality` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.SupportedExteriorClassArrows` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.SupportedExteriorClasses` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.SupportedHomAdjunctionTranspose` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.SupportedHomPullback` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.SupportedProjectionSplitting` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.SupportedSectionsHom` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.SupportedTwistDegreeZeroProduct` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.SupportedTwistMultiplication` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.SupportedTwistPullback` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.TraceFormulaTopologicalInvariance` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.TwistFrobeniusScalar` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.VectorBundleThomClass` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.WeilCohomologyScalarExtensionQlbar` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.WeilFourierInversion` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.WeilFourierPlancherel` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.WeilOne` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.Paper.ZlShriekComposition` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.SecSmoothPurity.FiniteGeneralRing` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.SecSmoothPurity.PurityDncCoefficientTransport` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.SecSmoothPurity.RationalPurityTraceCoherence` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.SecSmoothPurity.ReductionCompatibilities` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.SecSmoothPurity.SmoothPurityNaturality` | unclaimed | No change in types or definitions; no adaptation. |
| `Sheaf.ZetaWeil.WeightPurityRoots` | unclaimed | No change in types or definitions; no adaptation. |
| `TargetsCheck` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Concentration` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.DegreeOne` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Exactness` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierWeight` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.LocalDuality` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Perverse` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Purity` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.RealPushforward` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Upper` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.UpperReduction` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.AffineCurve` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.CompactSupport` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.DirectImage` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.FibreCohomology` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.FiniteMap` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.FormalSteps` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.MixedStalk` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.OpenLine` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.RealCurve` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.RealSheaves` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.Statement` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.WeilSheaf.AffineLineCohomology` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.WeilSheaf.CohomologicalRange` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.WeilSheaf.CohomologicalRangeAffine` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.WeilSheaf.Curve` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.WeilSheaf.CurveEndpoints` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.WeilSheaf.EulerProduct` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierInversion` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierInversion.Composite` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierInversion.Delta` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierInversion.OtherSections` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierInversion.Vanishing` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierPlancherel` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierStalk` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierTrace` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.WeilSheaf.GrothendieckLefschetz` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.WeilSheaf.LFunction` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.WeilSheaf.LowerShriekFunctoriality` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.WeilSheaf.LowerShriekOperations` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.WeilSheaf.LowerShriekPackage` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.WeilSheaf.OpenClosedTriangle` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.WeilSheaf.RealPurity` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.WeilSheaf.VerdierDual` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.WeilSheaf.VerdierDualFinite` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.WeilSheaf.VerdierDualLocalization` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.ZetaFunction.BettiSymmetry` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.ZetaFunction.CohomologicalFamily` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.ZetaFunction.DualityReciprocity` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.ZetaFunction.Examples` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.ZetaFunction.ExamplesCohomology` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.ZetaFunction.FinalTheorems` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.ZetaFunction.HasseWeil` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.ZetaFunction.IntegralFactors` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.ZetaFunction.IntegralFrobeniusFactors` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.ZetaFunction.LissePurity` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.ZetaFunction.Rationality` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.ZetaFunction.RealizationIndependence` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.ZetaFunction.RelativePurity` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.ZetaFunction.SmoothProper` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.ZetaFunction.TraceFormula` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.ZetaFunction.WeightSeparation` | unclaimed | No change in types or definitions; no adaptation. |
| `WeilConjectures.ZetaFunction.Weights` | unclaimed | No change in types or definitions; no adaptation. |

## Status

landed 20261019T122545-L-466311 2026-10-19 (merge of deliver/G5/Sheaf.SecSmoothPurity.ProEtaleFiniteConstantSections)
