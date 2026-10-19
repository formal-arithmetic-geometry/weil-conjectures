# Rep.isZero_dvr_galois_cohomology

## Reason

The existing module-wide `warningAsError` setting also applies to diagnostic commands
appended by the delivery's axiom probe. Scope it to the theorem being proved. This keeps
warning checking on the proof while allowing the generated diagnostic commands to run.
The preflight conservatively classifies changes to module-level commands as an interface
change, so this record documents the complete effect. No existing declaration's signature,
visibility or mathematical definition changes.

## Old

```lean
set_option autoImplicit false
set_option warningAsError true

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace Rep

/-- The existing theorem docstring. -/
theorem isZero_dvr_galois_cohomology
```

## New

```lean
set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace Rep

set_option warningAsError true in
/-- The existing theorem docstring. -/
theorem isZero_dvr_galois_cohomology
```

The docstring and the complete theorem signature are identical to the existing module;
the displayed placeholder abbreviates that unchanged docstring only. The changed command
itself is verbatim in each excerpt. Existing public imports are unchanged. Proof imports
are replaced by the two proved supporting results documented in the report and DAG.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RepresentationTheory.DvrGalois | Y2 | Warning policy scoped to its theorem; its statement is unchanged. |
| Sheaf.AlgebraicGeometry.CurveOpenDimensionGeneral | claimed | No adaptation; no exported declaration or type changed. |
| Sheaf.AlgebraicGeometry.OpenComplementKnown | claimed | No adaptation; no exported declaration or type changed. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | No adaptation; no exported declaration or type changed. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | No adaptation; no exported declaration or type changed. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed | No adaptation; no exported declaration or type changed. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | No adaptation; no exported declaration or type changed. |
| Sheaf.Paper.AdicPurityFiniteTensor | claimed | No adaptation; no exported declaration or type changed. |
| Sheaf.Paper.AdicPurityObjects | unclaimed | No adaptation; no exported declaration or type changed. |
| Sheaf.Paper.AdicPurityRootComparisons | claimed | No adaptation; no exported declaration or type changed. |
| Sheaf.Paper.AdicPuritySourceReduction | claimed | No adaptation; no exported declaration or type changed. |
| Sheaf.Paper.AdicPurityTwistReduction | claimed | No adaptation; no exported declaration or type changed. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | No adaptation; no exported declaration or type changed. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | No adaptation; no exported declaration or type changed. |
| Sheaf.Paper.ChernFlagFormula | claimed | No adaptation; no exported declaration or type changed. |
| Sheaf.Paper.CohomologicalSmoothnessTheorem | unclaimed | No adaptation; no exported declaration or type changed. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | claimed | No adaptation; no exported declaration or type changed. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | No adaptation; no exported declaration or type changed. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | No adaptation; no exported declaration or type changed. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | No adaptation; no exported declaration or type changed. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | No adaptation; no exported declaration or type changed. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | No adaptation; no exported declaration or type changed. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | No adaptation; no exported declaration or type changed. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | claimed | No adaptation; no exported declaration or type changed. |
| Sheaf.Paper.FiniteReductionAffineOrientation | claimed | No adaptation; no exported declaration or type changed. |
| Sheaf.Paper.FiniteReductionChartCalculus | claimed | No adaptation; no exported declaration or type changed. |
| Sheaf.Paper.FiniteReductionComparisons | claimed | No adaptation; no exported declaration or type changed. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | No adaptation; no exported declaration or type changed. |
| Sheaf.Paper.FiniteReductionRootCharts | claimed | No adaptation; no exported declaration or type changed. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | claimed | No adaptation; no exported declaration or type changed. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | No adaptation; no exported declaration or type changed. |
| Sheaf.Paper.FlagLocalComparison | unclaimed | No adaptation; no exported declaration or type changed. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | No adaptation; no exported declaration or type changed. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | No adaptation; no exported declaration or type changed. |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | unclaimed | No adaptation; no exported declaration or type changed. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | No adaptation; no exported declaration or type changed. |
| Sheaf.Paper.LocalizedTopChern | claimed | No adaptation; no exported declaration or type changed. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | No adaptation; no exported declaration or type changed. |
| Sheaf.Paper.PurAdicReconstruction | claimed | No adaptation; no exported declaration or type changed. |
| Sheaf.Paper.PurityAffineLineOrientation | claimed | No adaptation; no exported declaration or type changed. |
| Sheaf.Paper.PurityAffineLineOrientationUniqueness | claimed | No adaptation; no exported declaration or type changed. |
| Sheaf.Paper.PurityChernClasses | unclaimed | No adaptation; no exported declaration or type changed. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | No adaptation; no exported declaration or type changed. |
| Sheaf.Paper.PurityDiagonalBaseChangeCompared | claimed | No adaptation; no exported declaration or type changed. |
| Sheaf.Paper.PurityDiagonalDualizingObject | claimed | No adaptation; no exported declaration or type changed. |
| Sheaf.Paper.PurityDiagonalSectionPasting | unclaimed | No adaptation; no exported declaration or type changed. |
| Sheaf.Paper.PurityDncComparisons | claimed | No adaptation; no exported declaration or type changed. |
| Sheaf.Paper.PurityDncFamilyIntrinsic | unclaimed | No adaptation; no exported declaration or type changed. |
| Sheaf.Paper.PurityDncInvariance | unclaimed | No adaptation; no exported declaration or type changed. |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | claimed | No adaptation; no exported declaration or type changed. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | claimed | No adaptation; no exported declaration or type changed. |
| Sheaf.Paper.RationalPurityPresentation | unclaimed | No adaptation; no exported declaration or type changed. |
| Sheaf.Paper.RationalSmoothPurityCanonical | claimed | No adaptation; no exported declaration or type changed. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | No adaptation; no exported declaration or type changed. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | No adaptation; no exported declaration or type changed. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | No adaptation; no exported declaration or type changed. |
| Sheaf.Paper.SmoothPurityMap | claimed | No adaptation; no exported declaration or type changed. |
| Sheaf.Paper.SmoothTrace | unclaimed | No adaptation; no exported declaration or type changed. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | No adaptation; no exported declaration or type changed. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | No adaptation; no exported declaration or type changed. |
| Sheaf.Paper.TwistFrobeniusScalar | claimed | No adaptation; no exported declaration or type changed. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | No adaptation; no exported declaration or type changed. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | No adaptation; no exported declaration or type changed. |
| Sheaf.Paper.WeilFourierInversion | claimed | No adaptation; no exported declaration or type changed. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | No adaptation; no exported declaration or type changed. |
| Sheaf.Paper.WeilOne | unclaimed | No adaptation; no exported declaration or type changed. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | No adaptation; no exported declaration or type changed. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | claimed | No adaptation; no exported declaration or type changed. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | claimed | No adaptation; no exported declaration or type changed. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | unclaimed | No adaptation; no exported declaration or type changed. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | claimed | No adaptation; no exported declaration or type changed. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | No adaptation; no exported declaration or type changed. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | No adaptation; no exported declaration or type changed. |
| TargetsCheck | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.Statement | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.WeilSheaf.CohomologicalRange | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.WeilSheaf.CurveTopCohomology | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.WeilSheaf.FourierPlancherel | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.WeilSheaf.FourierStalk | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.WeilSheaf.FourierTrace | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.WeilSheaf.LissePoincarePairing | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.WeilSheaf.LowerShriekPackage | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.WeilSheaf.OpenClosedTriangle | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.WeilSheaf.PoincareDualityLisse | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.WeilSheaf.VerdierDual | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | No adaptation; no exported declaration or type changed. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | No adaptation; no exported declaration or type changed. |

The table lists all 178 transitive consumers (the same set returned by
`tools/downstream.py`). None needs source adaptation. The warning option governs elaboration within the
item file and changes no imported mathematical interface. The four new supporting modules
add proved results without replacing existing declarations; their definitions construct
actual submodules and quotient actions. No target statement or definition it uses changes,
so this command-scope adjustment does not reopen a target statement review.

## Status

landed 20261019T192855-L-1878877 2026-10-19 (merge of deliver/Y2/Sheaf.RepresentationTheory.DvrGalois)
