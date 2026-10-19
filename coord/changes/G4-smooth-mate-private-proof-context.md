# AlgebraicGeometry.ProEtale.smoothMate_counit_cancellation

## Reason

Preflight classifies the declaration-scoped transparency options and `omit` commands
around new private helpers as a context change. This record documents their scope.
Every existing declaration signature, visibility, attribute, docstring, definition
body and public import is unchanged. All nine new helpers are private and proved.
The existing theorem's proof is completed. No target meaning changes.

## Old

There were no private helpers or their scoped commands. The existing theorem's
unchanged signature ended with:

```lean
            (DerivedCategory.Plus.ι.map a)) := by
  sorry
```

## New

The theorem has the identical signature and a complete proof from the nine private
helpers. Each helper has these declaration-scoped elaboration options:

```lean
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
```

The following commands apply only to the private helper they precede, omitting
unused section instances from that helper's inferred arguments:

```lean
omit [Finite Λ] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] in
omit [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] in
omit [Finite Λ] in
```

No global option, variable, instance, notation or attribute is added or changed.
Seven redundant proof-only imports are removed, as listed in report.md.
No consumer adaptation is needed: public signatures, data and imports are identical,
and private proof elaboration commands are not exported.

## Users

Current transitive importers are listed below, from `tools/downstream.py`.
Textual declaration-use search finds no consumer mentioning the theorem by name;
the direct importer is `Sheaf.Paper.SmoothExceptionalBaseChangeStatement`.
Holders are read from the shared claim snapshot. No consumer is changed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Identical public interface; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.AdicPurityFiniteTensor | W8 | Identical public interface; no adaptation. |
| Sheaf.Paper.AdicPurityObjects | W9 | Identical public interface; no adaptation. |
| Sheaf.Paper.AdicPurityRootComparisons | X5 | Identical public interface; no adaptation. |
| Sheaf.Paper.AdicPuritySourceReduction | X6 | Identical public interface; no adaptation. |
| Sheaf.Paper.AdicPurityTwistReduction | X8 | Identical public interface; no adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.ChernFlagFormula | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothnessTheorem | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | G6 | Identical public interface; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | H7 | Identical public interface; no adaptation. |
| Sheaf.Paper.FiniteReductionAffineOrientation | T6 | Identical public interface; no adaptation. |
| Sheaf.Paper.FiniteReductionChartCalculus | S7 | Identical public interface; no adaptation. |
| Sheaf.Paper.FiniteReductionComparisons | T7 | Identical public interface; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.FiniteReductionRootCharts | D8 | Identical public interface; no adaptation. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | V6 | Identical public interface; no adaptation. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.LocalizedTopChern | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | H8 | Identical public interface; no adaptation. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.PurityDiagonalBaseChangeCompared | F1 | Identical public interface; no adaptation. |
| Sheaf.Paper.PurityDiagonalDualizingObject | G3 | Identical public interface; no adaptation. |
| Sheaf.Paper.PurityDiagonalSectionPasting | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.PurityDncComparisons | G3 | Identical public interface; no adaptation. |
| Sheaf.Paper.PurityDncFamilyIntrinsic | E3 | Identical public interface; no adaptation. |
| Sheaf.Paper.PurityDncInvariance | H2 | Identical public interface; no adaptation. |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | K6 | Identical public interface; no adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | K7 | Identical public interface; no adaptation. |
| Sheaf.Paper.RationalSmoothPurityCanonical | W5 | Identical public interface; no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.SmoothExceptionalBaseChangeStatement | M9 | Identical public interface; no adaptation. |
| Sheaf.Paper.SmoothPurityMap | R2 | Identical public interface; no adaptation. |
| Sheaf.Paper.SmoothTrace | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.TwistFrobeniusScalar | G4 | Identical public interface; no adaptation. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.WeilFourierInversion | J6 | Identical public interface; no adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.WeilOne | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Identical public interface; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | D6 | Identical public interface; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | E6 | Identical public interface; no adaptation. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Identical public interface; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Identical public interface; no adaptation. |
| TargetsCheck | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.Statement | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRange | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.WeilSheaf.FourierPlancherel | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.WeilSheaf.FourierStalk | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.WeilSheaf.FourierTrace | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekPackage | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.WeilSheaf.OpenClosedTriangle | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDual | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | X5 | Identical public interface; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Identical public interface; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Identical public interface; no adaptation. |

## Status

landed 20261019T093415-L-2307478 2026-10-19 (merge of deliver/G4/Sheaf.Paper.SmoothMateCounitCancellation)
