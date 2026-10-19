# proEtale_tensor_composition_unit

## Reason

Record the local irreducibility attributes conservatively classified as an interface
change by preflight. They prevent elaboration of this proof from repeatedly unfolding
large concrete pullback and adjunction constructions. Each attribute is explicitly
`local`; no reducibility setting is exported to any importing module. All existing
public signatures, definitions, public imports, instances and visibility are identical.
No target definition or statement changes meaning.

## Old

No local irreducibility attributes in this module.

## New

```lean
attribute [local irreducible] proEtaleRingModulePullbackObj
  proEtaleRingModulePullbackMap proEtaleRingModuleAdjunction

attribute [local irreducible] proEtaleRingModulePullback
```

Both commands are inside `namespace AlgebraicGeometry.Scheme`. The first precedes the
private proof helpers, and the second precedes the existing public theorem. None occurs
inside or changes either existing public generator/scalar definition.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.ProEtaleTensorCompositionUnit --uses
proEtale_tensor_composition_unit` reports no external textual use of the theorem and
106 transitive importers. All are listed below. The three direct importers retain the
same public environment: proof-only imports were removed, new helpers are private, and
the irreducibility attributes are local. Their unchanged source copies compiled
against the candidate in a separate scratchpad compile, without delivering their files:
`FrobeniusTrivializationPullback` (8.1 s), `AmbientProperOpenPasting` (13.7 s), and
`GraphFrobeniusOpenExchange` (25.3 s); the candidate compiled in 22.9 s.
No consumer needs adaptation; no consumer signature becomes stronger or weaker.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ProEtaleTensorCompositionUnit | K4 | Sole sorry proved; public API unchanged. |
| Sheaf.AlgebraicGeometry.AbsoluteFrobeniusCoefficientNaturality | unclaimed | Public API unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FrobeniusStalkTrivializationNormalization | W7 | Public API unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FrobeniusTrivializationPullback | B7 | Public API unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison | P9 | Public API unchanged; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Public API unchanged; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | unclaimed | Public API unchanged; no adaptation. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unclaimed | Public API unchanged; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Public API unchanged; no adaptation. |
| Sheaf.Paper.ChernFlagFormula | unclaimed | Public API unchanged; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | P2 | Public API unchanged; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Public API unchanged; no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | A4 | Public API unchanged; no adaptation. |
| Sheaf.Paper.ConstantExtensionCompactComparison | unclaimed | Public API unchanged; no adaptation. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | J4 | Public API unchanged; no adaptation. |
| Sheaf.Paper.CoprojectionCompositionMate | unclaimed | Public API unchanged; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Public API unchanged; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Public API unchanged; no adaptation. |
| Sheaf.Paper.DlConstantFieldCharts | G8 | Public API unchanged; no adaptation. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | H7 | Public API unchanged; no adaptation. |
| Sheaf.Paper.FiniteProductCompactification | unclaimed | Public API unchanged; no adaptation. |
| Sheaf.Paper.FlagLocalComparison | unclaimed | Public API unchanged; no adaptation. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Public API unchanged; no adaptation. |
| Sheaf.Paper.FrobeniusCoefficientReductionCoherence | X3 | Public API unchanged; no adaptation. |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | A5 | Public API unchanged; no adaptation. |
| Sheaf.Paper.GeneralCondensedWeilRealization | unclaimed | Public API unchanged; no adaptation. |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | unclaimed | Public API unchanged; no adaptation. |
| Sheaf.Paper.IteratedWeilCocycle | D4 | Public API unchanged; no adaptation. |
| Sheaf.Paper.IteratedWeilMap | unclaimed | Public API unchanged; no adaptation. |
| Sheaf.Paper.LocalFrobeniusConjugacy | Q5 | Public API unchanged; no adaptation. |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | A6 | Public API unchanged; no adaptation. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | Public API unchanged; no adaptation. |
| Sheaf.Paper.LocalizedTopChern | unclaimed | Public API unchanged; no adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | Public API unchanged; no adaptation. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Public API unchanged; no adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | K7 | Public API unchanged; no adaptation. |
| Sheaf.Paper.RationalStalkExact | A7 | Public API unchanged; no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Public API unchanged; no adaptation. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | Public API unchanged; no adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Public API unchanged; no adaptation. |
| Sheaf.Paper.SystemCompactificationProjectionSubstitution | F5 | Public API unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | unclaimed | Public API unchanged; no adaptation. |
| Sheaf.Paper.VectorBundleThomClass | X2 | Public API unchanged; no adaptation. |
| Sheaf.Paper.WeilConstantExtensionFrobenius | unclaimed | Public API unchanged; no adaptation. |
| Sheaf.Paper.WeilOne | unclaimed | Public API unchanged; no adaptation. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | S2 | Public API unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility | unclaimed | Public API unchanged; no adaptation. |
| Sheaf.SixFunctors.AmbientProperOpenPasting | N2 | Public API unchanged; no adaptation. |
| Sheaf.SixFunctors.CompositionProjectionMate | V5 | Public API unchanged; no adaptation. |
| Sheaf.SixFunctors.GraphFrobeniusOpenExchange | B5 | Public API unchanged; no adaptation. |
| Sheaf.SixFunctors.SchemeGaloisCoefficientChange | E4 | Public API unchanged; no adaptation. |
| Sheaf.SixFunctors.SchemeGaloisComparison | unclaimed | Public API unchanged; no adaptation. |
| Sheaf.SixFunctors.SchemeGeometricFrobenius | F3 | Public API unchanged; no adaptation. |
| Sheaf.SixFunctors.SelectedSchemeGaloisComparison | X5 | Public API unchanged; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Public API unchanged; no adaptation. |
| TargetsCheck | unclaimed | Public API unchanged; no adaptation. |
| WeilConjectures | unclaimed | Public API unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Public API unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | Public API unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Public API unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Public API unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed | Public API unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Public API unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Public API unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | Public API unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | Public API unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | Public API unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Public API unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Public API unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Public API unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | Public API unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Public API unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Public API unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Public API unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Public API unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Public API unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Public API unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Public API unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Public API unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Public API unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Public API unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Public API unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Public API unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Public API unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | Public API unchanged; no adaptation. |
| WeilConjectures.Statement | unclaimed | Public API unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | Public API unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | Public API unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | Public API unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | Public API unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | Public API unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | Public API unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekPackage | unclaimed | Public API unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Public API unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Public API unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Public API unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Public API unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Public API unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Public API unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Public API unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Public API unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | Public API unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Public API unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Public API unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Public API unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Public API unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Public API unchanged; no adaptation. |

## Status

landed 20261019T160420-L-3355581 2026-10-19 (merge of deliver/K4/Sheaf.AlgebraicGeometry.ProEtaleTensorCompositionUnit)
