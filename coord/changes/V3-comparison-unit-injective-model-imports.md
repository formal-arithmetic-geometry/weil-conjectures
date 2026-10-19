# AlgebraicGeometry.ProEtale.comparisonUnitInjectiveModel

## Reason

The existing normalized `Adjunction.derivedPlus_unit_app_fac` formula and naturality
of `rightDerivedFunctorPlusUnit` give the resolution representative directly. Remove
unused resolution and K-injective proof imports and the unrelated public imports of
`CompactSupportComparisonUnit` and `ComparisonPullbackExact`.

Every declaration signature, universe, visibility and definition is unchanged.
Both direct consumers import this item privately and already explicitly import both
removed public modules, so their proof environments lose nothing. Consequently
all transitive consumers retain the same public interfaces. No adapted module is
included and no target statement review is reopened.

## Old

```lean
public import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonDerived
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.Paper.ComparisonPullbackExact
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.Algebra.Homology.BoundedBelowInjectiveResolution
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
```

## New

```lean
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonDerived
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
```

## Users

The downstream scan was run before pruning, including
`tools/downstream.py Sheaf.Paper.PurityComparisonUnitInjectiveModel --uses
comparisonUnitInjectiveModel`. No other module currently mentions the theorem by name.
No module below is edited; holder entries are therefore inapplicable to forced adaptation.
The two direct private importers each have explicit imports of both removed modules.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SupportComparisonBoundary | not adapted | Direct private importer; both removed modules explicitly imported; unchanged. |
| Sheaf.AlgebraicGeometry.SupportedBottomGluing | not adapted | Direct private importer; both removed modules explicitly imported; unchanged. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.Composition | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityExceptionalReduction | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityFiniteTensor | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityObjects | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityRootComparisons | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.Paper.AdicPuritySourceReduction | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityTwistReduction | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.Paper.CartierClassAgreement | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.Paper.ChernFlagFormula | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothnessTheorem | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.Paper.DualizingObjectPurity | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionAffineOrientation | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionChartCalculus | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionComparisons | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionRootCharts | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.Paper.FlagPullbackInjective | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.Paper.FourierTraceFormula | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.Paper.LocalizedTopChern | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.Paper.PurityAffineLineOrientation | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.Paper.PurityAffineLineOrientationUniqueness | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.Paper.PurityChernClasses | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.Paper.PurityCompositionCoherence | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.Paper.PurityDiagonalBaseChangeCompared | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.Paper.PurityDiagonalDualizingObject | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.Paper.PurityDiagonalSectionPasting | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.Paper.PurityDivisorClass | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.Paper.PurityDncComparisons | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.Paper.PurityDncFamilyIntrinsic | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.Paper.PurityDncInvariance | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.Paper.PurityFrameIndependence | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.Paper.PurityRankOneLocalCalculation | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.Paper.RationalSmoothPurityCanonical | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.Paper.RegularImmersionPurityComparison | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.Paper.RelativeSupportBottomDescent | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityMap | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.Paper.SmoothTrace | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.Paper.TwistFrobeniusScalar | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.Paper.VectorBundleThomClass | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.Paper.WeilFourierInversion | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.Paper.WeilOne | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.Paper.ZlShriekComposition | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| TargetsCheck | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.Statement | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRange | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.CurveEndpoints | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.EulerProduct | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierPlancherel | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierStalk | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierTrace | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LFunction | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekPackage | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.OpenClosedTriangle | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDual | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.LissePurity | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.Rationality | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.Paper.RegularImmersionCancellation | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.Paper.RegularImmersionClassData | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.Paper.RegularImmersionExteriorClass | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.Paper.RegularImmersionPurity | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.Paper.RegularImmersionSignedEvaluation | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | not adapted | Transitive consumer; public interfaces unchanged; no adaptation. |

## Status

landed 20261019T112554-L-3956558 2026-10-19 (merge of deliver/V3/Sheaf.Paper.PurityComparisonUnitInjectiveModel)
