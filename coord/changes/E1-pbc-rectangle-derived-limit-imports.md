# AlgebraicGeometry.ProEtale.pbcRectangleDerivedLimit: public import pruning

## Reason

The theorem already receives F, its shift and triangulated structures, the natural
Roos first arrow p, and the commuting tower rectangle as hypotheses. Its proof uses
only functoriality, naturality, associativity and the product projection identity.
The sequential derived-limit construction is unnecessary. Replace its public import
by the precise Mathlib interface needed by the existing F.IsTriangulated hypothesis.
Also remove two unused proof imports. No signature, definition, visibility, instance,
notation, target meaning or declaration docstring changes.

## Old

```lean
public import Sheaf.Paper.PbcRoosTriangle
public import Sheaf.Paper.SequentialDerivedInverseLimitFunctor
import Sheaf.Paper.CompletedRlimFunctor
import Sheaf.Paper.CompletedTowerCompatibility
```

## New

```lean
public import Sheaf.Paper.PbcRoosTriangle
public import Mathlib.CategoryTheory.Triangulated.Functor
```

## Users

The source scan with tools/downstream.py found 176 transitive importers.
Its --uses scan found no external textual use of pbcRectangleDerivedLimit.
The sole direct importer is Sheaf.Paper.CompletedMapReduction, which imports this
module privately. Its original source compiled unchanged against the pruned module
using lcompile.py in a two-file set (3.6 seconds for this item, 4.6 for the consumer).
Thus the removed re-export does not propagate through that consumer's public API.
Both declarations of this item retain their exact signatures, values and visibility,
except that the theorem now has a complete proof. No consumer adaptation is delivered.
Holders below are a coordination snapshot.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.SfEtaleExchanges | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.AlgebraicGeometry.SfFiniteEtaleProjectionFormula | H2 | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.DeligneLaumon.GenericDualityModel | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.Paper.AdicExceptionalBase | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.Paper.AdicExceptionalCoherence | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.Paper.AdicExceptionalComposition | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.Paper.AdicExceptionalOperations | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.Paper.AdicExceptionalProjection | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.Paper.AdicExceptionalProjectionData | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.Paper.AdicExceptionalScalars | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.Paper.ChernFlagFormula | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | G6 | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.Paper.CompactFiberStalk | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.Paper.CompactSupportLerayFiltration | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.Paper.CompleteCompactSupportProetale | J3 | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.Paper.CompleteProetale | S6 | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.Paper.CompleteProetaleStrictTowerRealization | Y7 | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.Paper.CompletedCompactSupportExchange | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.Paper.CompletedMapReduction | R4 | Direct importer: original source compiled against delivered module; no adaptation. |
| Sheaf.Paper.ConstructibleCompleteBaseChange | K1 | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.Paper.DlConstantFieldCharts | G8 | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.Paper.FieldShriekLowerBound | F1 | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.Paper.FieldWeilShriekShiftData | G1 | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | H7 | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.Paper.FiniteExtensionCompactSupportBaseChange | N2 | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.Paper.FiniteExtensionProperBaseChange | N3 | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.Paper.FiniteRegularReductionDualizing | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.Paper.FourierKernelConvolution | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.Paper.FrobeniusCompactSupportExchange | F6 | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.Paper.GeometricFiberFiniteExtension | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.Paper.GeometricFiberQbar | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.Paper.LocalizedTopChern | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.Paper.NormalizedCoefficientFamilies | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.Paper.QbarCompactSupportBaseChange | S4 | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.Paper.QbarMiddleTStructure | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.Paper.QbarProperBaseChange | T1 | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | K7 | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.Paper.RationalCompactSupportCoefficientCoherence | P2 | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.Paper.SfExchanges | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.Paper.WeilFourierInversion | J6 | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.Paper.WeilMixedUpperBounds | R3 | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.Paper.WeilOne | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.Paper.WeilShriekShiftCompatibility | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.Paper.ZlFrameworkOpenExchange | Q8 | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.Paper.ZlFrameworkPbcOpenComparisonData | P7 | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.Paper.ZlFrameworkPbcOpenExchangeComparison | R5 | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.Paper.ZlOpenDiagramComparisonTransport | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.SixFunctors.ArbitraryFieldVerdier | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.SixFunctors.IntegralOperationShiftData | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.SixFunctors.QbarDualRecollement | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| TargetsCheck | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.Statement | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRange | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.WeilSheaf.FourierPlancherel | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.WeilSheaf.FourierStalk | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.WeilSheaf.FourierTrace | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekPackage | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.WeilSheaf.OpenClosedTriangle | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDual | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | X5 | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Indirect importer; no exported declaration changed; no adaptation. |

## Status

landed 20261019T093338-L-2297955 2026-10-19 (merge of deliver/E1/Sheaf.Paper.PbcRectangleDerivedLimit)
