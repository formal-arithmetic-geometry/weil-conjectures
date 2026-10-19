# Sheaf.Paper.CompactSupportExchangeTransport proof elaboration commands

## Reason

The stage-3 static interface comparison flags the added options, scoped variables,
and local instance attributes as command changes. Record them explicitly for review.
They support private categorical proof helpers and elaboration of the proof. The
four public definitions and the public theorem signature remain verbatim identical;
no mathematical definition, statement, universe or visibility changes. The local
attributes are not exported, and the helper variables are confined to
`section ExactComparisons`, which ends before the public definitions. The options
control elaboration, not the logic or any downstream declaration.

The complete item compiled in 27.1 seconds. Three unused simp arguments have since
been removed; the delivery tool checks the cleaned file. No compiler limit is raised.
No consumer adaptation is required. No target meaning changes or new nodes result.

## Old

The original non-import command sequence (whitespace normalized by `leanindex`):

```lean
module
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
```

## New

The new non-import command sequence (same normalization):

```lean
module
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
variable {C D E : Type*} [Category C] [Category D] [Category E] [Abelian C] [Abelian D] [Abelian E] [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
```

All added declarations are private proved theorems. The existing four definition
bodies are unchanged. Three unused proof imports are removed and two proof imports
are added, as detailed in report.md; the public imports are unchanged.

## Users

Generated from `tools/downstream.py Sheaf.Paper.CompactSupportExchangeTransport
--uses compactExchangeTransportComparison compactExchangeTransportSource
compactExchangeTransportTarget compactExchangeTransportAtWitness
compactSupport_exchange_transport`; current holders are read from the coordination
claim records. Direct textual users are `CompactSupportSiteCoherence` and
`SmoothMateCounitCancellation`; the remaining consumers are transitive importers.
No listed consumer is edited.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.ProjectionComparisonEtaleOrigin` | A2 | no adaptation; public API unchanged |
| `Sheaf.DeligneLaumon.GenericDualityModel` | unclaimed | no adaptation; public API unchanged |
| `Sheaf.DeligneLaumon.QbarCurveDuality` | unclaimed | no adaptation; public API unchanged |
| `Sheaf.DeligneLaumon.Reduction.AffineCurveUpper` | unclaimed | no adaptation; public API unchanged |
| `Sheaf.DeligneLaumon.Reduction.Composition` | unclaimed | no adaptation; public API unchanged |
| `Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift` | unclaimed | no adaptation; public API unchanged |
| `Sheaf.Paper.AdicPurityExceptionalReduction` | unclaimed | no adaptation; public API unchanged |
| `Sheaf.Paper.AdicPurityFiniteTensor` | W8 | no adaptation; public API unchanged |
| `Sheaf.Paper.AdicPurityObjects` | unclaimed | no adaptation; public API unchanged |
| `Sheaf.Paper.AdicPurityRootComparisons` | X5 | no adaptation; public API unchanged |
| `Sheaf.Paper.AdicPuritySourceReduction` | X6 | no adaptation; public API unchanged |
| `Sheaf.Paper.AdicPurityTwistReduction` | X8 | no adaptation; public API unchanged |
| `Sheaf.Paper.AdicSmoothDualizingComplexes` | unclaimed | no adaptation; public API unchanged |
| `Sheaf.Paper.AdmissibleVerdierExchange` | unclaimed | no adaptation; public API unchanged |
| `Sheaf.Paper.ArithmeticRoots` | unclaimed | no adaptation; public API unchanged |
| `Sheaf.Paper.ChernFlagFormula` | G4 | no adaptation; public API unchanged |
| `Sheaf.Paper.CohomologicalSmoothComposition` | unclaimed | no adaptation; public API unchanged |
| `Sheaf.Paper.CohomologicalSmoothEtaleLocality` | unclaimed | no adaptation; public API unchanged |
| `Sheaf.Paper.CohomologicalSmoothnessTheorem` | unclaimed | no adaptation; public API unchanged |
| `Sheaf.Paper.CommonStageConstituentNonexceptional` | P2 | no adaptation; public API unchanged |
| `Sheaf.Paper.CommonStageFourierWeightUpper` | unclaimed | no adaptation; public API unchanged |
| `Sheaf.Paper.CompactSupportExchangeTransport` | B4 | proof and private helpers; public API unchanged |
| `Sheaf.Paper.CompactSupportSiteCoherence` | U2 | no adaptation; public API unchanged |
| `Sheaf.Paper.CompletedStalkFrobeniusReduction` | A4 | no adaptation; public API unchanged |
| `Sheaf.Paper.CompletedTensorHomTranspose` | D2 | no adaptation; public API unchanged |
| `Sheaf.Paper.CurveIntermediateExtension` | unclaimed | no adaptation; public API unchanged |
| `Sheaf.Paper.CurveMiddleExtensionUpper` | unclaimed | no adaptation; public API unchanged |
| `Sheaf.Paper.DualizingObjectPurity` | unclaimed | no adaptation; public API unchanged |
| `Sheaf.Paper.EtaleRhoMonoidalMate` | unclaimed | no adaptation; public API unchanged |
| `Sheaf.Paper.ExtensionByZeroPunctual` | unclaimed | no adaptation; public API unchanged |
| `Sheaf.Paper.FiniteCoefficientSmoothPurity` | unclaimed | no adaptation; public API unchanged |
| `Sheaf.Paper.FiniteEtaleLisseWeilImage` | H7 | no adaptation; public API unchanged |
| `Sheaf.Paper.FiniteFreeCompactSupportComposition` | U5 | no adaptation; public API unchanged |
| `Sheaf.Paper.FiniteReductionAffineOrientation` | T6 | no adaptation; public API unchanged |
| `Sheaf.Paper.FiniteReductionChartCalculus` | S7 | no adaptation; public API unchanged |
| `Sheaf.Paper.FiniteReductionComparisons` | T7 | no adaptation; public API unchanged |
| `Sheaf.Paper.FiniteReductionOfPurity` | unclaimed | no adaptation; public API unchanged |
| `Sheaf.Paper.FiniteReductionRootCharts` | D8 | no adaptation; public API unchanged |
| `Sheaf.Paper.FiniteSmoothPullbackExchange` | V6 | no adaptation; public API unchanged |
| `Sheaf.Paper.FiniteStructuralMapsCommShift` | Y6 | no adaptation; public API unchanged |
| `Sheaf.Paper.FiniteTorStability` | unclaimed | no adaptation; public API unchanged |
| `Sheaf.Paper.FiniteUniversalSmoothTrace` | unclaimed | no adaptation; public API unchanged |
| `Sheaf.Paper.FixedStalkIdentificationReduction` | W4 | no adaptation; public API unchanged |
| `Sheaf.Paper.FlagLocalComparison` | unclaimed | no adaptation; public API unchanged |
| `Sheaf.Paper.FlagPullbackInjective` | unclaimed | no adaptation; public API unchanged |
| `Sheaf.Paper.FourierTraceFormula` | unclaimed | no adaptation; public API unchanged |
| `Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology` | unclaimed | no adaptation; public API unchanged |
| `Sheaf.Paper.LocalizedFlagProduct` | unclaimed | no adaptation; public API unchanged |
| `Sheaf.Paper.LocalizedTopChern` | E5 | no adaptation; public API unchanged |
| `Sheaf.Paper.ProjectiveBundleFormula` | unclaimed | no adaptation; public API unchanged |
| `Sheaf.Paper.PurAdicReconstruction` | H8 | no adaptation; public API unchanged |
| `Sheaf.Paper.PurityChernClasses` | unclaimed | no adaptation; public API unchanged |
| `Sheaf.Paper.PurityCompositionCoherence` | unclaimed | no adaptation; public API unchanged |
| `Sheaf.Paper.PurityDiagonalBaseChangeCompared` | R3 | no adaptation; public API unchanged |
| `Sheaf.Paper.PurityDiagonalDualizingObject` | G3 | no adaptation; public API unchanged |
| `Sheaf.Paper.PurityDiagonalSectionPasting` | unclaimed | no adaptation; public API unchanged |
| `Sheaf.Paper.PurityDncComparisons` | G3 | no adaptation; public API unchanged |
| `Sheaf.Paper.PurityDncFamilyIntrinsic` | unclaimed | no adaptation; public API unchanged |
| `Sheaf.Paper.PurityDncInvariance` | unclaimed | no adaptation; public API unchanged |
| `Sheaf.Paper.PuritySectionInvariantIntrinsic` | K6 | no adaptation; public API unchanged |
| `Sheaf.Paper.QbarMiddleTStructure` | unclaimed | no adaptation; public API unchanged |
| `Sheaf.Paper.QbarPerverseSubcategories` | unclaimed | no adaptation; public API unchanged |
| `Sheaf.Paper.QbarPerverseSupportCondition` | unclaimed | no adaptation; public API unchanged |
| `Sheaf.Paper.QuasiFiniteCompactSupportWeights` | K7 | no adaptation; public API unchanged |
| `Sheaf.Paper.RationalPurityPresentation` | unclaimed | no adaptation; public API unchanged |
| `Sheaf.Paper.RationalScalarTransposeCompatibility` | K8 | no adaptation; public API unchanged |
| `Sheaf.Paper.RationalSmoothPurityCanonical` | W5 | no adaptation; public API unchanged |
| `Sheaf.Paper.RationalWeilPurityNaturalityMate` | unclaimed | no adaptation; public API unchanged |
| `Sheaf.Paper.RegularImmersionPurityComparison` | unclaimed | no adaptation; public API unchanged |
| `Sheaf.Paper.SfBidualityClass` | C6 | no adaptation; public API unchanged |
| `Sheaf.Paper.SixFunctorOperationDatum` | unclaimed | no adaptation; public API unchanged |
| `Sheaf.Paper.SixFunctorOperationDatumStages` | unclaimed | no adaptation; public API unchanged |
| `Sheaf.Paper.SmoothMateCounitCancellation` | unclaimed | no adaptation; public API unchanged |
| `Sheaf.Paper.SmoothProperPurityHypotheses` | unclaimed | no adaptation; public API unchanged |
| `Sheaf.Paper.SmoothPullbackSupportDimension` | unclaimed | no adaptation; public API unchanged |
| `Sheaf.Paper.SmoothPurityMap` | R2 | no adaptation; public API unchanged |
| `Sheaf.Paper.SmoothTrace` | unclaimed | no adaptation; public API unchanged |
| `Sheaf.Paper.SupportedProjectionSplitting` | unclaimed | no adaptation; public API unchanged |
| `Sheaf.Paper.TateTwistSupportCondition` | unclaimed | no adaptation; public API unchanged |
| `Sheaf.Paper.TraceFormulaTopologicalInvariance` | unclaimed | no adaptation; public API unchanged |
| `Sheaf.Paper.TwistFrobeniusScalar` | G4 | no adaptation; public API unchanged |
| `Sheaf.Paper.VectorBundleThomClass` | unclaimed | no adaptation; public API unchanged |
| `Sheaf.Paper.WeilCohomologyScalarExtensionQlbar` | unclaimed | no adaptation; public API unchanged |
| `Sheaf.Paper.WeilFourierInversion` | J6 | no adaptation; public API unchanged |
| `Sheaf.Paper.WeilFourierPlancherel` | unclaimed | no adaptation; public API unchanged |
| `Sheaf.Paper.WeilOne` | unclaimed | no adaptation; public API unchanged |
| `Sheaf.Paper.ZlShriekComposition` | unclaimed | no adaptation; public API unchanged |
| `Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility` | unclaimed | no adaptation; public API unchanged |
| `Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization` | unclaimed | no adaptation; public API unchanged |
| `Sheaf.SecSmoothPurity.FiniteGeneralRing` | D6 | no adaptation; public API unchanged |
| `Sheaf.SecSmoothPurity.PurityDncCoefficientTransport` | K9 | no adaptation; public API unchanged |
| `Sheaf.SecSmoothPurity.RationalPurityTraceCoherence` | unclaimed | no adaptation; public API unchanged |
| `Sheaf.SecSmoothPurity.ReductionCompatibilities` | E6 | no adaptation; public API unchanged |
| `Sheaf.SecSmoothPurity.SmoothPurityNaturality` | unclaimed | no adaptation; public API unchanged |
| `Sheaf.SixFunctors.ArbitraryFieldVerdier` | unclaimed | no adaptation; public API unchanged |
| `Sheaf.SixFunctors.CoefDualFormulaScalarTranspose` | unclaimed | no adaptation; public API unchanged |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtension` | A9 | no adaptation; public API unchanged |
| `Sheaf.SixFunctors.CoefQbarVerdier` | R5 | no adaptation; public API unchanged |
| `Sheaf.SixFunctors.CoefTowerNaturalCurrying` | F2 | no adaptation; public API unchanged |
| `Sheaf.SixFunctors.FiniteExceptional` | unclaimed | no adaptation; public API unchanged |
| `Sheaf.SixFunctors.FiniteMappingAdjunction` | J7 | no adaptation; public API unchanged |
| `Sheaf.SixFunctors.IntegralDualizing` | unclaimed | no adaptation; public API unchanged |
| `Sheaf.SixFunctors.IntegralVerdier` | V2 | no adaptation; public API unchanged |
| `Sheaf.SixFunctors.QbarDualRecollement` | unclaimed | no adaptation; public API unchanged |
| `Sheaf.SixFunctors.RationalOperations` | unclaimed | no adaptation; public API unchanged |
| `Sheaf.SixFunctors.RationalRetractEvaluation` | A4 | no adaptation; public API unchanged |
| `Sheaf.SixFunctors.RationalVerdier` | V4 | no adaptation; public API unchanged |
| `Sheaf.ZetaWeil.WeightPurityRoots` | unclaimed | no adaptation; public API unchanged |
| `TargetsCheck` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.DeligneLaumon.AffineLine.Concentration` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.DeligneLaumon.AffineLine.DegreeOne` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.DeligneLaumon.AffineLine.Exactness` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierWeight` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.DeligneLaumon.AffineLine.LocalDuality` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.DeligneLaumon.AffineLine.Perverse` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.DeligneLaumon.AffineLine.Purity` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.DeligneLaumon.AffineLine.RealPushforward` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.DeligneLaumon.AffineLine.Upper` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.DeligneLaumon.AffineLine.UpperReduction` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.DeligneLaumon.Reduction.AffineCurve` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.DeligneLaumon.Reduction.CompactSupport` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.DeligneLaumon.Reduction.DirectImage` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.DeligneLaumon.Reduction.FibreCohomology` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.DeligneLaumon.Reduction.FiniteMap` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.DeligneLaumon.Reduction.FormalSteps` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.DeligneLaumon.Reduction.MixedStalk` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.DeligneLaumon.Reduction.OpenLine` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.DeligneLaumon.Reduction.RealCurve` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.DeligneLaumon.Reduction.RealSheaves` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Adic` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Rational` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.SixFunctors.Adic.Reduction` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.SixFunctors.Etale.Derived.ClosedUpperShriekCoproducts` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.SixFunctors.Etale.Derived.CompactConstructible` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.SixFunctors.Etale.Derived.CompactSupportIntegral` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.SixFunctors.Etale.Derived.ExcisionComparison` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactLocalizing` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekLocalizing` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.Statement` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.WeilSheaf.AffineLineCohomology` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.WeilSheaf.CohomologicalRange` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.WeilSheaf.CohomologicalRangeAffine` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.WeilSheaf.Curve` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.WeilSheaf.CurveEndpoints` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.WeilSheaf.CurveTopCohomology` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.WeilSheaf.EulerProduct` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.WeilSheaf.FourierInversion` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.WeilSheaf.FourierInversion.Composite` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.WeilSheaf.FourierInversion.Delta` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.WeilSheaf.FourierInversion.OtherSections` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.WeilSheaf.FourierInversion.Vanishing` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.WeilSheaf.FourierPlancherel` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.WeilSheaf.FourierStalk` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.WeilSheaf.FourierTrace` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.WeilSheaf.GrothendieckLefschetz` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.WeilSheaf.LFunction` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.WeilSheaf.LissePoincarePairing` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.WeilSheaf.LocalizationRational` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.WeilSheaf.LowerShriekFunctoriality` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.WeilSheaf.LowerShriekOperations` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.WeilSheaf.LowerShriekPackage` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.WeilSheaf.OpenClosedTriangle` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.WeilSheaf.PoincareDualityLisse` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.WeilSheaf.RealPurity` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.WeilSheaf.TraceIsomorphism` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.WeilSheaf.VerdierDual` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.WeilSheaf.VerdierDualFinite` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.WeilSheaf.VerdierDualLocalization` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.ZetaFunction.BettiSymmetry` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.ZetaFunction.CohomologicalFamily` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.ZetaFunction.DualityReciprocity` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.ZetaFunction.Examples` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.ZetaFunction.ExamplesCohomology` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.ZetaFunction.FinalTheorems` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.ZetaFunction.HasseWeil` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.ZetaFunction.IntegralFactors` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.ZetaFunction.IntegralFrobeniusFactors` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.ZetaFunction.LissePurity` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.ZetaFunction.Rationality` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.ZetaFunction.RealizationIndependence` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.ZetaFunction.RelativePurity` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.ZetaFunction.SmoothProper` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.ZetaFunction.TraceFormula` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.ZetaFunction.WeightSeparation` | unclaimed | no adaptation; public API unchanged |
| `WeilConjectures.ZetaFunction.Weights` | unclaimed | no adaptation; public API unchanged |

## Status

landed 20261019T192648-L-1852260 2026-10-19 (merge of deliver/B4/Sheaf.Paper.CompactSupportExchangeTransport)
