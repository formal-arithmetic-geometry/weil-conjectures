# Sheaf.RepresentationTheory.ProcyclicTwoTerm: scoped proof infrastructure

## Reason

The stage-3 proof needs private finite-sum, two-term-complex and delta-functor helpers.
Preflight classified the added `variable`, `open` and local `attribute` commands as a
change requiring an interface record. All added commands and instances are now scoped
inside a section that ends before the existing public theorem. In particular `ttAdditive`
is a private local instance. The theorem signature and public imports remain verbatim
unchanged; this record documents proof infrastructure, not a mathematical definition repair.

## Old

The public theorem is preceded only by the original namespace opening:

```lean
open CategoryTheory CategoryTheory.Limits

namespace Rep
```

## New

The same public opening remains. A section contains the new private helpers and ends
before the original public theorem. The additional scoped controls are:

```lean
section

open ZeroObject
set_option linter.style.haveILetI false
open scoped BigOperators
open Topology

-- Private proved finite-sum helpers.
namespace Rep
variable {A : Type u} [Ring A] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

-- Private local preadditive instances and private proved complex helpers.
attribute [local instance 4000] Preadditive.preadditiveHasZeroMorphisms
attribute [local instance 3000] ttPreadditive ttModulePreadditive
-- ttAdditive is declared with `private local instance`.

end Rep
end

namespace Rep
```

No existing declaration signature, visibility or public import changes. All new
instances are local to the proof-helper section. No new instance is exported.

## Users

`tools/downstream.py Sheaf.RepresentationTheory.ProcyclicTwoTerm --uses
Rep.exists_procyclic_twoTerm_computation` lists 183 transitive consumers and no textual
caller outside the item. The three direct importers are KummerRootRegularDivisorPurity,
SemistableCoordinateDivisorPurity and DvrGalois. Their unchanged public imports and
statements need no adaptation. Original scratch copies of all three compile against the
delivered module, in 7.4, 5.7 and 5.3 seconds respectively. The following table records the full transitive inventory;
all effects are proof-only and no consumer file is delivered. Holdings are from the
read-only claim records at the time of this check.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CurveOpenDimensionGeneral | claimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.KummerRootRegularDivisorPurity | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.LogSmoothTraitPunctualPurity | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.MonomialTraitPunctualPurity | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.OpenComplementKnown | claimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SemistableCoordinateDivisorPurity | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityFiniteTensor | claimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityObjects | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityRootComparisons | claimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.AdicPuritySourceReduction | claimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityTwistReduction | claimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ChernFlagFormula | claimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothnessTheorem | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | claimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | claimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionAffineOrientation | claimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionChartCalculus | claimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionComparisons | claimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionRootCharts | claimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | claimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FlagLocalComparison | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.LocalizedTopChern | claimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | claimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.PurityAffineLineOrientation | claimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.PurityAffineLineOrientationUniqueness | claimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.PurityDiagonalBaseChangeCompared | claimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.PurityDiagonalDualizingObject | claimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.PurityDiagonalSectionPasting | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.PurityDncComparisons | claimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.PurityDncFamilyIntrinsic | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.PurityDncInvariance | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | claimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | claimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.RationalPurityPresentation | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.RationalSmoothPurityCanonical | claimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityMap | claimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.SmoothTrace | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.TwistFrobeniusScalar | claimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.WeilFourierInversion | claimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.WeilOne | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.RepresentationTheory.DvrGalois | claimed | Public interface unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | claimed | Public interface unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | claimed | Public interface unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | claimed | Public interface unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Public interface unchanged; no adaptation. |
| TargetsCheck | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.Statement | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRange | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.CurveTopCohomology | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierPlancherel | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierStalk | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierTrace | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LissePoincarePairing | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekPackage | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.OpenClosedTriangle | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.PoincareDualityLisse | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDual | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Public interface unchanged; no adaptation. |

## Status

landed 20261019T192646-L-1852070 2026-10-19 (merge of deliver/B2/Sheaf.RepresentationTheory.ProcyclicTwoTerm)
