# AlgebraicGeometry.ProEtale.spEtaleMate_transpose

## Reason

The item theorem is now proved using the existing categorical projection mate
calculation and the normalized bounded-below direct-image comparison. This is a
proof-only implementation change; no public mathematical statement is changed.

## Old

The module contained one postponed proof of
`AlgebraicGeometry.ProEtale.spEtaleMate_transpose`, using the earlier generic
ringed-topos proof dependencies. The existing namespace opening was:

```lean
open CategoryTheory CategoryTheory.Limits
```

There was no local irreducibility attribute for `MonoidalCategory.curriedTensor`.

## New

The theorem is proved by private transport and counit-normalization helpers,
using `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjComparison`.
The public declarations and signatures remain identical. The only module-local
interface changes are the following module-local commands:

```lean
open CategoryTheory.Functor
attribute [local irreducible] MonoidalCategory.curriedTensor
```

## Users

The source dependency audit found 215 downstream modules. None uses
`spEtaleMate_transpose` by name yet, and no exported declaration or public import
changes. Every consumer therefore keeps the same interface and meaning. Holders
are not involved because no consumer is edited.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.DeligneLaumon.GenericDualityModel` | not adapted | unchanged interface and meaning |
| `Sheaf.DeligneLaumon.Reduction.AffineCurveUpper` | not adapted | unchanged interface and meaning |
| `Sheaf.DeligneLaumon.Reduction.Composition` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.AdicExceptionalCoherence` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.AdicExceptionalComposition` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.AdicExceptionalProjection` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.AdicExceptionalScalars` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.AdicPurityExceptionalReduction` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.AdicPurityFiniteTensor` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.AdicPurityObjects` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.AdicPurityRootComparisons` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.AdicPuritySourceReduction` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.AdicPurityTwistReduction` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.AdicSmoothDualizingComplexes` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.ArithmeticRoots` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.ChernFlagFormula` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.CoefficientTowerShriekCalculus` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.CohomologicalSmoothEtaleLocality` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.CommonStageConstituentNonexceptional` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.CommonStageFourierWeightUpper` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.CurveIntermediateExtension` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.CurveMiddleExtensionUpper` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.DualizingObjectPurity` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.EtaleProEtaleCoefficientCompatibility` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.ExtensionByZeroPunctual` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.FiniteCoefficientAdjointComparisons` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.FiniteCoefficientSmoothPurity` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.FiniteEtaleLisseWeilImage` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.FiniteReductionAffineOrientation` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.FiniteReductionChartCalculus` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.FiniteReductionComparisons` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.FiniteReductionOfPurity` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.FiniteReductionRootCharts` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.FiniteRegularReductionDualizing` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.FiniteSmoothPullbackExchange` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.FiniteTorStability` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.FixedStalkIdentificationReduction` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.FlagPullbackInjective` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.FourierTraceFormula` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.IntegralDirectImageTower` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.LocalizedTopChern` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.ProjectiveBundleFormula` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.PurAdicReconstruction` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.PurityChernClasses` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.PurityCompositionCoherence` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.PurityDiagonalDualizingObject` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.PurityDncInvariance` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.QbarMiddleTStructure` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.QbarPerverseSubcategories` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.QbarPerverseSupportCondition` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.QuasiFiniteCompactSupportWeights` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.RationalPurityPresentation` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.RationalSmoothPurityCanonical` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.RationalWeilPurityNaturalityMate` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.RegularImmersionPurityComparison` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.SfBidualityClass` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.SmoothPullbackSupportDimension` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.SmoothPurityMap` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.SmoothTrace` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.SupportedProjectionSplitting` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.TateTwistSupportCondition` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.TraceFormulaDualizingComplex` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.TraceFormulaTopologicalInvariance` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.TwistFrobeniusScalar` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.VaryingRingGraphSummand` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.VectorBundleThomClass` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.VerdierExchange` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.WeilCohomologyScalarExtensionQlbar` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.WeilFourierInversion` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.WeilFourierPlancherel` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.WeilOne` | not adapted | unchanged interface and meaning |
| `Sheaf.Paper.ZlShriekComposition` | not adapted | unchanged interface and meaning |
| `Sheaf.SecSmoothPurity.FiniteGeneralRing` | not adapted | unchanged interface and meaning |
| `Sheaf.SecSmoothPurity.MixedBaseChange` | not adapted | unchanged interface and meaning |
| `Sheaf.SecSmoothPurity.PurityDncCoefficientTransport` | not adapted | unchanged interface and meaning |
| `Sheaf.SecSmoothPurity.ReductionCompatibilities` | not adapted | unchanged interface and meaning |
| `Sheaf.SecSmoothPurity.ReductionDirectImage` | not adapted | unchanged interface and meaning |
| `Sheaf.SecSmoothPurity.ReductionExceptional` | not adapted | unchanged interface and meaning |
| `Sheaf.SecSmoothPurity.RestrictionTransitionTranspose` | not adapted | unchanged interface and meaning |
| `Sheaf.SecSmoothPurity.SmoothPurityNaturality` | not adapted | unchanged interface and meaning |
| `Sheaf.SixFunctors.ArbitraryFieldVerdier` | not adapted | unchanged interface and meaning |
| `Sheaf.SixFunctors.CoefDualFormulaScalarTranspose` | not adapted | unchanged interface and meaning |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtension` | not adapted | unchanged interface and meaning |
| `Sheaf.SixFunctors.CoefQbarVerdier` | not adapted | unchanged interface and meaning |
| `Sheaf.SixFunctors.CoefTowerEvaluationPairing` | not adapted | unchanged interface and meaning |
| `Sheaf.SixFunctors.CoefTowerTraceRectification` | not adapted | unchanged interface and meaning |
| `Sheaf.SixFunctors.FiniteCoefficientVerdier` | not adapted | unchanged interface and meaning |
| `Sheaf.SixFunctors.FiniteDualizing` | not adapted | unchanged interface and meaning |
| `Sheaf.SixFunctors.IntegralDualizing` | not adapted | unchanged interface and meaning |
| `Sheaf.SixFunctors.IntegralVerdier` | not adapted | unchanged interface and meaning |
| `Sheaf.SixFunctors.QbarDualRecollement` | not adapted | unchanged interface and meaning |
| `Sheaf.SixFunctors.RationalOperations` | not adapted | unchanged interface and meaning |
| `Sheaf.SixFunctors.RationalVerdier` | not adapted | unchanged interface and meaning |
| `Sheaf.ZetaWeil.WeightPurityRoots` | not adapted | unchanged interface and meaning |
| `TargetsCheck` | not adapted | unchanged interface and meaning |
| `WeilConjectures` | not adapted | unchanged interface and meaning |
| `WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper` | not adapted | unchanged interface and meaning |
| `WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform` | not adapted | unchanged interface and meaning |
| `WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights` | not adapted | unchanged interface and meaning |
| `WeilConjectures.DeligneLaumon.AffineLine.Concentration` | not adapted | unchanged interface and meaning |
| `WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist` | not adapted | unchanged interface and meaning |
| `WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound` | not adapted | unchanged interface and meaning |
| `WeilConjectures.DeligneLaumon.AffineLine.DegreeOne` | not adapted | unchanged interface and meaning |
| `WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional` | not adapted | unchanged interface and meaning |
| `WeilConjectures.DeligneLaumon.AffineLine.Exactness` | not adapted | unchanged interface and meaning |
| `WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents` | not adapted | unchanged interface and meaning |
| `WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary` | not adapted | unchanged interface and meaning |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude` | not adapted | unchanged interface and meaning |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport` | not adapted | unchanged interface and meaning |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierWeight` | not adapted | unchanged interface and meaning |
| `WeilConjectures.DeligneLaumon.AffineLine.LocalDuality` | not adapted | unchanged interface and meaning |
| `WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension` | not adapted | unchanged interface and meaning |
| `WeilConjectures.DeligneLaumon.AffineLine.Perverse` | not adapted | unchanged interface and meaning |
| `WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform` | not adapted | unchanged interface and meaning |
| `WeilConjectures.DeligneLaumon.AffineLine.Purity` | not adapted | unchanged interface and meaning |
| `WeilConjectures.DeligneLaumon.AffineLine.RealPushforward` | not adapted | unchanged interface and meaning |
| `WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel` | not adapted | unchanged interface and meaning |
| `WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy` | not adapted | unchanged interface and meaning |
| `WeilConjectures.DeligneLaumon.AffineLine.Upper` | not adapted | unchanged interface and meaning |
| `WeilConjectures.DeligneLaumon.AffineLine.UpperReduction` | not adapted | unchanged interface and meaning |
| `WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension` | not adapted | unchanged interface and meaning |
| `WeilConjectures.DeligneLaumon.Reduction.AffineCurve` | not adapted | unchanged interface and meaning |
| `WeilConjectures.DeligneLaumon.Reduction.CompactSupport` | not adapted | unchanged interface and meaning |
| `WeilConjectures.DeligneLaumon.Reduction.DirectImage` | not adapted | unchanged interface and meaning |
| `WeilConjectures.DeligneLaumon.Reduction.FibreCohomology` | not adapted | unchanged interface and meaning |
| `WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage` | not adapted | unchanged interface and meaning |
| `WeilConjectures.DeligneLaumon.Reduction.FiniteMap` | not adapted | unchanged interface and meaning |
| `WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension` | not adapted | unchanged interface and meaning |
| `WeilConjectures.DeligneLaumon.Reduction.FormalSteps` | not adapted | unchanged interface and meaning |
| `WeilConjectures.DeligneLaumon.Reduction.MixedStalk` | not adapted | unchanged interface and meaning |
| `WeilConjectures.DeligneLaumon.Reduction.OpenLine` | not adapted | unchanged interface and meaning |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed` | not adapted | unchanged interface and meaning |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk` | not adapted | unchanged interface and meaning |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing` | not adapted | unchanged interface and meaning |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights` | not adapted | unchanged interface and meaning |
| `WeilConjectures.DeligneLaumon.Reduction.RealCurve` | not adapted | unchanged interface and meaning |
| `WeilConjectures.DeligneLaumon.Reduction.RealSheaves` | not adapted | unchanged interface and meaning |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine` | not adapted | unchanged interface and meaning |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep` | not adapted | unchanged interface and meaning |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity` | not adapted | unchanged interface and meaning |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants` | not adapted | unchanged interface and meaning |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional` | not adapted | unchanged interface and meaning |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev` | not adapted | unchanged interface and meaning |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations` | not adapted | unchanged interface and meaning |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension` | not adapted | unchanged interface and meaning |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity` | not adapted | unchanged interface and meaning |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin` | not adapted | unchanged interface and meaning |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity` | not adapted | unchanged interface and meaning |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity` | not adapted | unchanged interface and meaning |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants` | not adapted | unchanged interface and meaning |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity` | not adapted | unchanged interface and meaning |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations` | not adapted | unchanged interface and meaning |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary` | not adapted | unchanged interface and meaning |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Adic` | not adapted | unchanged interface and meaning |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Rational` | not adapted | unchanged interface and meaning |
| `WeilConjectures.SixFunctors.Adic.Reduction` | not adapted | unchanged interface and meaning |
| `WeilConjectures.SixFunctors.Etale.Derived.ClosedUpperShriekCoproducts` | not adapted | unchanged interface and meaning |
| `WeilConjectures.SixFunctors.Etale.Derived.CompactConstructible` | not adapted | unchanged interface and meaning |
| `WeilConjectures.SixFunctors.Etale.Derived.CompactSupportIntegral` | not adapted | unchanged interface and meaning |
| `WeilConjectures.SixFunctors.Etale.Derived.ExcisionComparison` | not adapted | unchanged interface and meaning |
| `WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients` | not adapted | unchanged interface and meaning |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral` | not adapted | unchanged interface and meaning |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport` | not adapted | unchanged interface and meaning |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational` | not adapted | unchanged interface and meaning |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil` | not adapted | unchanged interface and meaning |
| `WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization` | not adapted | unchanged interface and meaning |
| `WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars` | not adapted | unchanged interface and meaning |
| `WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension` | not adapted | unchanged interface and meaning |
| `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactLocalizing` | not adapted | unchanged interface and meaning |
| `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekLocalizing` | not adapted | unchanged interface and meaning |
| `WeilConjectures.Statement` | not adapted | unchanged interface and meaning |
| `WeilConjectures.WeilSheaf.AffineLineCohomology` | not adapted | unchanged interface and meaning |
| `WeilConjectures.WeilSheaf.CohomologicalRange` | not adapted | unchanged interface and meaning |
| `WeilConjectures.WeilSheaf.CohomologicalRangeAffine` | not adapted | unchanged interface and meaning |
| `WeilConjectures.WeilSheaf.Curve` | not adapted | unchanged interface and meaning |
| `WeilConjectures.WeilSheaf.CurveEndpoints` | not adapted | unchanged interface and meaning |
| `WeilConjectures.WeilSheaf.EulerProduct` | not adapted | unchanged interface and meaning |
| `WeilConjectures.WeilSheaf.FourierInversion` | not adapted | unchanged interface and meaning |
| `WeilConjectures.WeilSheaf.FourierInversion.Composite` | not adapted | unchanged interface and meaning |
| `WeilConjectures.WeilSheaf.FourierInversion.Delta` | not adapted | unchanged interface and meaning |
| `WeilConjectures.WeilSheaf.FourierInversion.OtherSections` | not adapted | unchanged interface and meaning |
| `WeilConjectures.WeilSheaf.FourierInversion.Vanishing` | not adapted | unchanged interface and meaning |
| `WeilConjectures.WeilSheaf.FourierPlancherel` | not adapted | unchanged interface and meaning |
| `WeilConjectures.WeilSheaf.FourierStalk` | not adapted | unchanged interface and meaning |
| `WeilConjectures.WeilSheaf.FourierTrace` | not adapted | unchanged interface and meaning |
| `WeilConjectures.WeilSheaf.GrothendieckLefschetz` | not adapted | unchanged interface and meaning |
| `WeilConjectures.WeilSheaf.LFunction` | not adapted | unchanged interface and meaning |
| `WeilConjectures.WeilSheaf.LocalizationRational` | not adapted | unchanged interface and meaning |
| `WeilConjectures.WeilSheaf.LowerShriekFunctoriality` | not adapted | unchanged interface and meaning |
| `WeilConjectures.WeilSheaf.LowerShriekOperations` | not adapted | unchanged interface and meaning |
| `WeilConjectures.WeilSheaf.LowerShriekPackage` | not adapted | unchanged interface and meaning |
| `WeilConjectures.WeilSheaf.OpenClosedTriangle` | not adapted | unchanged interface and meaning |
| `WeilConjectures.WeilSheaf.RealPurity` | not adapted | unchanged interface and meaning |
| `WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity` | not adapted | unchanged interface and meaning |
| `WeilConjectures.WeilSheaf.VerdierDual` | not adapted | unchanged interface and meaning |
| `WeilConjectures.WeilSheaf.VerdierDualFinite` | not adapted | unchanged interface and meaning |
| `WeilConjectures.WeilSheaf.VerdierDualLocalization` | not adapted | unchanged interface and meaning |
| `WeilConjectures.ZetaFunction.BettiSymmetry` | not adapted | unchanged interface and meaning |
| `WeilConjectures.ZetaFunction.CohomologicalFamily` | not adapted | unchanged interface and meaning |
| `WeilConjectures.ZetaFunction.DualityReciprocity` | not adapted | unchanged interface and meaning |
| `WeilConjectures.ZetaFunction.Examples` | not adapted | unchanged interface and meaning |
| `WeilConjectures.ZetaFunction.ExamplesCohomology` | not adapted | unchanged interface and meaning |
| `WeilConjectures.ZetaFunction.FinalTheorems` | not adapted | unchanged interface and meaning |
| `WeilConjectures.ZetaFunction.HasseWeil` | not adapted | unchanged interface and meaning |
| `WeilConjectures.ZetaFunction.IntegralFactors` | not adapted | unchanged interface and meaning |
| `WeilConjectures.ZetaFunction.IntegralFrobeniusFactors` | not adapted | unchanged interface and meaning |
| `WeilConjectures.ZetaFunction.LissePurity` | not adapted | unchanged interface and meaning |
| `WeilConjectures.ZetaFunction.Rationality` | not adapted | unchanged interface and meaning |
| `WeilConjectures.ZetaFunction.RealizationIndependence` | not adapted | unchanged interface and meaning |
| `WeilConjectures.ZetaFunction.RelativePurity` | not adapted | unchanged interface and meaning |
| `WeilConjectures.ZetaFunction.SmoothProper` | not adapted | unchanged interface and meaning |
| `WeilConjectures.ZetaFunction.TraceFormula` | not adapted | unchanged interface and meaning |
| `WeilConjectures.ZetaFunction.WeightSeparation` | not adapted | unchanged interface and meaning |
| `WeilConjectures.ZetaFunction.Weights` | not adapted | unchanged interface and meaning |

## Status

landed 20261019T112600-L-3957919 2026-10-19 (merge of deliver/V4/Sheaf.Paper.SpDirectImageEtaleMate)

Item: `Sheaf.Paper.SpDirectImageEtaleMate`, held by V4. No other Lean module is changed.

## Reason and old/new versions

The old file has one postponed proof of `spEtaleMate_transpose`. The new file proves
it by the categorical projection/mate square, with private proved transport helpers.
The public declarations, their signatures, their definition bodies, and the public
imports are unchanged.

The proof adds `open CategoryTheory.Functor` to resolve bifunctor notation in the
private transport helper. This opens a namespace while elaborating this file;
it introduces no exported declaration or instance.

Immediately before the final theorem the proof adds
`attribute [local irreducible] MonoidalCategory.curriedTensor`. This prevents the
final concrete-coefficient specialization from unfolding tensor resolutions during
definitional comparison. The attribute is local to this module and does not alter
the definition, its value, or downstream elaboration. The private helpers and final
theorem also use declaration-local backward-definitional-equality options. No file
compile timeout or heartbeat limit is increased.

The proof-only imports `Sheaf.Paper.RingedExchangeTensorCoherence`,
`Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`, and
`Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap` are replaced by
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjComparison`.
The retained site-comparison import preserves the original unit dependency.

## Consumers and meaning

The direct importing module is `Sheaf.SecSmoothPurity.ReductionDirectImage`.
It currently imports this item without mentioning its declarations. The theorem
keeps the identical signature and canonical maps; no adaptation is necessary. All downstream target statements have the same meaning:
no exported definition, statement, instance, or public import changes. The newly
proved helpers are private and do not occur in public signatures or definitions.
The local namespace opening and local attribute cannot affect consumers.

## Validation

The retained clean compile log records success in 20.7 seconds, with no diagnostics.
The resumed delivery dry run compiled the current file and passed preflight;
its static and axiom checks accepted the complete delivery.
No direct `sorry` remains and no axiom or postponed theorem is added.
