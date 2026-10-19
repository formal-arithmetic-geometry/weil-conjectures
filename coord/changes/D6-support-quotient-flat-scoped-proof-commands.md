# SupportQuotientFlat scoped proof elaboration commands

## Reason

The completed proof introduces private helper declarations preceded by declaration-scoped
`omit` and `set_option ... in` commands. The static interface check conservatively flags
these as command changes. This record exposes them for independent review. They have
no effect on existing public signatures or definitions, module options for importers,
or any downstream statement. No consumer adaptation is necessary.

## Old

The only file-level option and shared section variables were, verbatim:

```lean
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

variable (A : Type u) [CommRing A] [Finite A]
  {C T : Scheme.{u}} (a : C ⟶ T) [IsClosedImmersion a]
```

## New

Those commands are unchanged. The new private helper declarations use the following
scoped commands, verbatim (some combinations occur before several private helpers):

```lean
omit [Finite A] in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
```

Each `omit ... in` applies only to the immediately following private declaration.
Each `set_option ... in` applies only to its following declaration. The setting
`respectTransparency true` also scopes the existing public theorem, preserving
its full signature. It limits automatic unfolding during instance inference;
the private helpers that require additional unfolding retain explicit `false`
settings. This fixes the resumed compiler timeout without changing any
definition, axiom, statement, or consumer. All new
helpers are private and completely proved; none occurs in a public definition or
signature. The seven existing definitions, existing theorem signature and all public
imports are byte-for-byte unchanged. The replacement theorem body and proof-only
imports do not alter any downstream proposition. The targets retain their meaning.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.SupportQuotientFlat --uses
AlgebraicGeometry.Scheme.supportQuotient_flat_kflat_stalk_comparison` lists 195
transitive importers and only the defining module as a textual declaration user.
Every listed importer is recorded below. Holders are from the local claim snapshot.
The effect is identical in every case because the entire existing public interface
is unchanged and all added elaboration commands are declaration-scoped.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SupportQuotientFlat | D6 | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.FlagLocalComparison | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.RationalPurityPresentation | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.CompactProductArrows | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.CompactProductRealizationArrows | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.KunnethSupported | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperSupportCompactMaps | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportComparisonBoundary | A3 | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportQuotientProduct | D7 | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportSiteComparison | S2 | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportedBottomGluing | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityFiniteTensor | W8 | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityObjects | W9 | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityRootComparisons | X5 | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.AdicPuritySourceReduction | X6 | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityTwistReduction | X8 | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.CartierClassAgreement | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.ChernFlagFormula | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothnessTheorem | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | G6 | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.CompactProductProperSupportCompatibility | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.CompactProductProperSupportLaws | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.CompactProductRealizationCoreLaws | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.CompactProductRealizationLaws | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.CompactProductTwistLaws | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | H7 | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionAffineOrientation | T6 | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionChartCalculus | S7 | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionComparisons | T7 | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionRootCharts | D8 | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | V6 | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.LocalizedTopChern | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | H8 | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.PurityAffineLineOrientation | J6 | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.PurityAffineLineOrientationUniqueness | E2 | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.PurityDiagonalBaseChangeCompared | F1 | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.PurityDiagonalDualizingObject | G3 | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.PurityDiagonalSectionPasting | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.PurityDivisorClass | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.PurityDncComparisons | G3 | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.PurityDncFamilyIntrinsic | E3 | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.PurityDncInvariance | H2 | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.PurityFrameIndependence | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.PurityRankOneLocalCalculation | F2 | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | K6 | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | K7 | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.RationalSmoothPurityCanonical | W5 | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.RegularImmersionCancellation | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.RegularImmersionClassData | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.RegularImmersionExteriorClass | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.RegularImmersionPurity | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.RegularImmersionSignedEvaluation | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.RelativeSupportBottomDescent | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityMap | R2 | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.SmoothTrace | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.SupportedClassGeometry | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.SupportedClassSiteComparison | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.SupportedExteriorClassArrows | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.SupportedExteriorShift | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.SupportedTwistDegreeZeroProduct | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.SupportedTwistMultiplication | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.SupportedTwistPullback | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.TwistFrobeniusScalar | G4 | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.WeilFourierInversion | J6 | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.WeilOne | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | D6 | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | E6 | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| TargetsCheck | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.Statement | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRange | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierPlancherel | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierStalk | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierTrace | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekPackage | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.OpenClosedTriangle | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDual | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | X5 | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Existing statements and definitions unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Existing statements and definitions unchanged; no adaptation. |

## Status

landed 20261019T192709-L-1856432 2026-10-19 (merge of deliver/D6/Sheaf.AlgebraicGeometry.SupportQuotientFlat)
