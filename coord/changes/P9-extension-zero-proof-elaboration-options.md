# AlgebraicGeometry.Scheme.cbc_extension_zero_stratified_perfect

## Reason

The completed proof uses explicit comparisons between the ordinary and normalized
completed-coefficient pullbacks. Two elaboration options in its module allow Lean
to identify the existing coefficient presentations and synthesize the composite
functor instances. Preflight classifies these added file-level commands as an
interface change, so this record documents them. They do not change a declaration,
a definition body, an instance registration, or a target statement. The settings
apply during elaboration of this file and are not exported to importers.

## Old

```lean
set_option autoImplicit false
```

## New

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
```

## Users

The source-only query
`python3 tools/downstream.py Sheaf.Paper.ExtensionZeroStratifiedPerfect --uses cbc_extension_zero_stratified_perfect`
reports 130 downstream modules and no external use of the theorem name. Every
one is listed below, together with the item itself. All existing public signatures,
public imports, and definition bodies remain identical. No consumer changes or
forced adaptations are needed. In particular, no target changes its meaning.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.DeligneLaumon.GenericDualityModel | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.AdicExceptionalBase | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.AdicExceptionalCoherence | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.AdicExceptionalComposition | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.AdicExceptionalOperations | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.AdicExceptionalProjection | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.AdicExceptionalProjectionData | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.AdicExceptionalScalars | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.ChernFlagFormula | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CompactFiberStalk | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CompactSupportLerayFiltration | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.ExtensionZeroStratifiedPerfect | P9 | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.FieldShriekLowerBound | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.FieldWeilShriekShiftData | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.FiniteExtensionCompactSupportBaseChange | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.FiniteRegularReductionDualizing | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.FourierKernelConvolution | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.IntegralCompactSupportUniformRestriction | W3 | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.LocalizedTopChern | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.QbarCompactSupportBaseChange | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.QbarMiddleTStructure | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.RationalCompactSupportCoefficientCoherence | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.RationalPurityPresentation | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.WeilFourierInversion | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.WeilMixedUpperBounds | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.WeilOne | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.WeilShriekShiftCompatibility | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.SixFunctors.ArbitraryFieldVerdier | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.SixFunctors.IntegralOperationShiftData | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.SixFunctors.QbarDualRecollement | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unclaimed | Same signatures and public imports; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Same signatures and public imports; no adaptation. |
| TargetsCheck | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.Statement | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Same signatures and public imports; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Same signatures and public imports; no adaptation. |

## Status

landed 20261019T093542-L-2325850 2026-10-19 (merge of deliver/P9/Sheaf.Paper.ExtensionZeroStratifiedPerfect)
