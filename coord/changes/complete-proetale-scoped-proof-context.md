# CompleteProetale scoped proof context

## Reason

The private scalar-comparison and homology proofs require permissive definitional
equality options and the Limits namespace. These commands are scoped to a section
ending before the public target theorem. The preflight conservatively flags the
changed command text. No mathematical statement, definition, public import or
existing signature changes. The new comparison lemma has its own node and module.

## Old

```lean
open CategoryTheory
namespace AlgebraicGeometry.Scheme
```

## New

```lean
open CategoryTheory
namespace AlgebraicGeometry.Scheme
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory.Limits
-- private proved helpers
end
```

## Users

A source-import graph audit found 177 transitive consumers; three
are direct importers. Only ConstructibleCompleteBaseChange mentions the target
name (in its docstring), and no consumer is edited. The earlier prescribed
`downstream.py --uses` attempt did not return before the process was interrupted;
the source graph was checked directly with rg over both library roots instead.
No target meaning changes and no target statement review is reopened.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.SfEtaleExchanges` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.AlgebraicGeometry.SfFiniteEtaleProjectionFormula` | H2 | Same public interface; no adaptation. |
| `Sheaf.DeligneLaumon.QbarCurveDuality` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.DeligneLaumon.Reduction.AffineCurveUpper` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.DeligneLaumon.Reduction.Composition` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.ArithmeticRoots` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.ChernFlagFormula` | G4 | Same public interface; no adaptation. |
| `Sheaf.Paper.CommonStageConstituentNonexceptional` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.CommonStageFourierWeightUpper` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.CompactFiberStalk` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.CompactSupportCondensedRealization` | U3 | Same public interface; no adaptation. |
| `Sheaf.Paper.CompactSupportLerayFiltration` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.CompleteCompactSupportProetale` | J3 | Same public interface; no adaptation. |
| `Sheaf.Paper.CompleteProetaleStrictTowerRealization` | Y7 | Same public interface; no adaptation. |
| `Sheaf.Paper.CompletedCompactSupportExchange` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.ConstructibleCompleteBaseChange` | K1 | Same public interface; no adaptation. |
| `Sheaf.Paper.CurveIntermediateExtension` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.CurveMiddleExtensionUpper` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.DlConstantFieldCharts` | G8 | Same public interface; no adaptation. |
| `Sheaf.Paper.DualBaseChange` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.ExchangeFunctoriality` | D6 | Same public interface; no adaptation. |
| `Sheaf.Paper.ExtensionByZeroPunctual` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.ExtensionZeroPerfectModelTransport` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.ExtensionZeroStratifiedPerfect` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.FieldShriekLowerBound` | F1 | Same public interface; no adaptation. |
| `Sheaf.Paper.FieldWeilShriekShiftData` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.FiniteEtaleLisseWeilImage` | H7 | Same public interface; no adaptation. |
| `Sheaf.Paper.FiniteExtensionCompactSupportBaseChange` | N2 | Same public interface; no adaptation. |
| `Sheaf.Paper.FiniteExtensionProperBaseChange` | C8 | Same public interface; no adaptation. |
| `Sheaf.Paper.FixProjectionCompactificationComparison` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.FlagLocalComparison` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.FlagPullbackInjective` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.FourierKernelConvolution` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.FourierTraceFormula` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.FrobeniusCompactSupportExchange` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.FrobeniusExchangeEquivalence` | V9 | Same public interface; no adaptation. |
| `Sheaf.Paper.GeneralCondensedWeilRealization` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.GeometricFiberFiniteExtension` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.GeometricFiberQbar` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.IntegralCompactSupportUniformRestriction` | W3 | Same public interface; no adaptation. |
| `Sheaf.Paper.LocalizedFlagProduct` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.LocalizedTopChern` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.NormalizedCoefficientFamilies` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.ProjectiveBundleFormula` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.PurityChernClasses` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.QbarCompactSupportBaseChange` | S4 | Same public interface; no adaptation. |
| `Sheaf.Paper.QbarProperBaseChange` | T1 | Same public interface; no adaptation. |
| `Sheaf.Paper.QuasiFiniteCompactSupportWeights` | K7 | Same public interface; no adaptation. |
| `Sheaf.Paper.RationalCompactSupportCoefficientCoherence` | P2 | Same public interface; no adaptation. |
| `Sheaf.Paper.RationalPurityPresentation` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.RationalWeilPurityNaturalityMate` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.SfExchanges` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.SmoothProperPurityHypotheses` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.SupportedProjectionSplitting` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.TraceFormulaTopologicalInvariance` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.VectorBundleThomClass` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.WeilCohomologyScalarExtensionQlbar` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.WeilFourierInversion` | J6 | Same public interface; no adaptation. |
| `Sheaf.Paper.WeilFourierPlancherel` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.WeilMixedUpperBounds` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.WeilShriekShiftCompatibility` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.ZlFrameworkOpenExchange` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.ZlFrameworkPbcOpenComparisonData` | P7 | Same public interface; no adaptation. |
| `Sheaf.Paper.ZlFrameworkPbcOpenExchangeComparison` | J7 | Same public interface; no adaptation. |
| `Sheaf.Paper.ZlFrobeniusCompactSupportComparison` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.ZlOpenDiagramComparisonTransport` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.ZlShriekComposition` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.SecSmoothPurity.RationalPurityTraceCoherence` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.SixFunctors.IntegralBasicOperationShift` | Z8 | Same public interface; no adaptation. |
| `Sheaf.SixFunctors.IntegralOperationShiftData` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.SixFunctors.IntegralRealizationShiftCoherence` | R5 | Same public interface; no adaptation. |
| `Sheaf.SixFunctors.SystemPrimitiveComparisonShift` | D6 | Same public interface; no adaptation. |
| `Sheaf.ZetaWeil.WeightPurityRoots` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Concentration` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.DegreeOne` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Exactness` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierWeight` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.LocalDuality` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Perverse` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Purity` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.RealPushforward` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Upper` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.UpperReduction` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.AffineCurve` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.CompactSupport` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.DirectImage` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.FibreCohomology` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.FiniteMap` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.FormalSteps` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.MixedStalk` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.OpenLine` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.RealCurve` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.RealSheaves` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.Statement` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.WeilSheaf.AffineLineCohomology` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.WeilSheaf.CohomologicalRange` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.WeilSheaf.CohomologicalRangeAffine` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.WeilSheaf.Curve` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.WeilSheaf.CurveEndpoints` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.WeilSheaf.CurveTopCohomology` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.WeilSheaf.EulerProduct` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierInversion` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierInversion.Composite` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierInversion.Delta` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierInversion.OtherSections` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierInversion.Vanishing` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierPlancherel` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierStalk` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierTrace` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.WeilSheaf.GrothendieckLefschetz` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.WeilSheaf.LFunction` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.WeilSheaf.LissePoincarePairing` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.WeilSheaf.LowerShriekFunctoriality` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.WeilSheaf.LowerShriekOperations` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.WeilSheaf.LowerShriekPackage` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.WeilSheaf.OpenClosedTriangle` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.WeilSheaf.PoincareDualityLisse` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.WeilSheaf.RealPurity` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.WeilSheaf.TraceIsomorphism` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.WeilSheaf.VerdierDual` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.WeilSheaf.VerdierDualFinite` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.WeilSheaf.VerdierDualLocalization` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.ZetaFunction.BettiSymmetry` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.ZetaFunction.CohomologicalFamily` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.ZetaFunction.DualityReciprocity` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.ZetaFunction.Examples` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.ZetaFunction.ExamplesCohomology` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.ZetaFunction.FinalTheorems` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.ZetaFunction.HasseWeil` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.ZetaFunction.IntegralFactors` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.ZetaFunction.IntegralFrobeniusFactors` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.ZetaFunction.LissePurity` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.ZetaFunction.Rationality` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.ZetaFunction.RealizationIndependence` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.ZetaFunction.RelativePurity` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.ZetaFunction.SmoothProper` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.ZetaFunction.TraceFormula` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.ZetaFunction.WeightSeparation` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.ZetaFunction.Weights` | unclaimed | Same public interface; no adaptation. |

## Status

landed 20261020T051451-L-1690650 2026-10-20 (merge of deliver/K5/Sheaf.Paper.CompleteProetale)
