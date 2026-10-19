# AlgebraicGeometry.ProEtale.openImmersionLowerShriek_localizing

## Reason

Complete the original theorem without changing its signature. Local proof elaboration uses
monoidal notation and object notation. It marks the large derived closed-monoidal structures,
pullback-from-the-point functor and extension-by-zero functor locally irreducible, avoiding
unnecessary unfolding in unification. These commands apply only in this module. All existing
public imports, declaration types, visibility and definitions remain unchanged. The new
private helpers are proved, and do not occur in any public signature or definition.

The stage-3 preflight conservatively flags the added open/scope/attribute commands as an
interface change and requests this record. None changes a target's mathematical meaning.

## Old

```lean
open CategoryTheory CategoryTheory.Limits
```

The original theorem has its existing signature followed by `:= by sorry`.

## New

```lean
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

open scoped CategoryTheory.Obj

attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed upperStarFromPoint
  CondensedRing.openImmersionLowerShriek
```

The original theorem has exactly the same signature and a complete proof. The existing
`set_option autoImplicit false` is retained. There are no new instances, public definitions,
notations, exported attributes or options, or changes to the existing public imports.

## Users

The table lists every transitive consumer in the current source import graph, as requested
by the downstream audit. For each consumer, the exported theorem and all other existing
public declarations have identical types; private proof declarations cannot be referenced
by its source. The added `open` commands are lexical, and `[local irreducible]` ends with
this module, so no consumer source needs adaptation. Holders are those recorded at audit.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology` | C8 | Unchanged signature and exports; no adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.DeligneLaumon.Reduction.AffineCurveUpper` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.DeligneLaumon.Reduction.Composition` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.AdicPurityExceptionalReduction` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.AdicPurityFiniteTensor` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.AdicPurityObjects` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.AdicPurityRootComparisons` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.AdicPuritySourceReduction` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.AdicPurityTwistReduction` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.AdicSmoothDualizingComplexes` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.AffineSpaceRationalInduction` | Q2 | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.ArithmeticRoots` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.BrownExceptionalAdjoint` | T6 | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.ClosedAdjointConstructibleYoneda` | M1 | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.CoefficientTowerShriekCalculus` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.CohomologicalSmoothEtaleLocality` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.CommonStageConstituentNonexceptional` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.CommonStageFourierWeightUpper` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.CompactificationCoherenceCocycle` | R4 | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.CompactificationLocalizing` | F4 | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.CompactificationRefinementLocalizing` | T9 | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.ConstructibleFiniteTorAdjunctions` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.CurveIntermediateExtension` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.CurveMiddleExtensionUpper` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.DetThmSfCtfStabilityInternalHom` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.DualizingObjectPurity` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.EtaleProEtaleAdjunctionTransfer` | V5 | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.EtaleProEtaleCoefficientCompatibility` | Y8 | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.ExceptionalInverseImageExistence` | U1 | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.ExtensionByZeroPunctual` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.FiniteCoefficientAdjointComparisons` | U2 | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.FiniteCoefficientSmoothPurity` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.FiniteLocalizingExceptionalPreservation` | Q7 | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.FiniteProperLocalizing` | V9 | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.FiniteReductionAffineOrientation` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.FiniteReductionChartCalculus` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.FiniteReductionComparisons` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.FiniteReductionOfPurity` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.FiniteReductionRootCharts` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.FiniteSmoothPullbackExchange` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.FiniteTorStability` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.FixedStalkIdentificationReduction` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.FourierTraceFormula` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.IntegralDirectImageTower` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.IntegralLocalizingProperBaseChange` | H2 | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.IntegralOpenImageProperFormulas` | R8 | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.IntegralProperProjectionFormula` | W9 | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.InterchangeProperPasting` | S4 | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.LocalizingExceptionalAdjoint` | J5 | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.LocalizingLowerShriekComposition` | A4 | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.MateOpenRestriction` | D7 | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.ModelCompactComparisonUnit` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.NonrationalLocalizingLowerShriekComposition` | B3 | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.ProEtaleProjectionExchangeMaps` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.ProEtaleProperOpenInterchange` | X6 | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.ProperExceptionalRestriction` | P2 | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.PurAdicReconstruction` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.PurityCompositionCoherence` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.PurityDiagonalDualizingObject` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.PurityDncInvariance` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.QbarPerverseSubcategories` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.QbarPerverseSupportCondition` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.QuasiFiniteCompactSupportWeights` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.RationalExceptionalRestriction` | K8 | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.RationalLocalizingProjectionFormula` | U4 | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.RationalPurityPresentation` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.RationalRestrictionGlue` | R9 | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.RationalSmoothPurityCanonical` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.RationalWeilPurityNaturalityMate` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.RegularImmersionPurityComparison` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.RestrictionLocal` | R3 | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.SfBidualityClass` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.SmoothPullbackSupportDimension` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.SmoothPurityMap` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.SmoothTrace` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.TateTwistSupportCondition` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.TowerCompactSupportProjectionFormula` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.TraceBaseChangeSecond` | E4 | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.TraceFormulaDualizingComplex` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.TraceFormulaTopologicalInvariance` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.UnboundedBaseChangeExtension` | K3 | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.VaryingRingGraphSummand` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.VerdierExchange` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.WeilFourierInversion` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.WeilFourierPlancherel` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.WeilOne` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.Paper.ZlShriekComposition` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.SecSmoothPurity.FiniteGeneralRing` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.SecSmoothPurity.MixedBaseChange` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.SecSmoothPurity.PurityDncCoefficientTransport` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.SecSmoothPurity.ReductionCompatibilities` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.SecSmoothPurity.ReductionDirectImage` | F1 | Unchanged signature and exports; no adaptation. |
| `Sheaf.SecSmoothPurity.ReductionExceptional` | F3 | Unchanged signature and exports; no adaptation. |
| `Sheaf.SecSmoothPurity.RestrictionTransitionTranspose` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.SecSmoothPurity.SmoothPurityNaturality` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.SixFunctors.CoefDualFormulaScalarTranspose` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtension` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.SixFunctors.CoefQbarVerdier` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.SixFunctors.CoefTowerEvaluationPairing` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.SixFunctors.CoefTowerTraceRectification` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.SixFunctors.CtfStabilityDirectImages` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.SixFunctors.DetSfCompCompositionBaseChange` | H6 | Unchanged signature and exports; no adaptation. |
| `Sheaf.SixFunctors.FiniteCoefficientVerdier` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.SixFunctors.FiniteDualizing` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.SixFunctors.IntegralBrownAdjoint` | M7 | Unchanged signature and exports; no adaptation. |
| `Sheaf.SixFunctors.IntegralDualizing` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.SixFunctors.IntegralExceptionalRestriction` | N4 | Unchanged signature and exports; no adaptation. |
| `Sheaf.SixFunctors.IntegralLocalizingCompactSupport` | T2 | Unchanged signature and exports; no adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionClosed` | U3 | Unchanged signature and exports; no adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionGlue` | G9 | Unchanged signature and exports; no adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionLine` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.SixFunctors.IntegralVerdier` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.SixFunctors.ProperImageLocalizingProper` | B4 | Unchanged signature and exports; no adaptation. |
| `Sheaf.SixFunctors.RationalOperations` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.SixFunctors.RationalVerdier` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.SmoothPurity.NormalizedWitness` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.Targets.AffineSpaceRationalLine` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.Targets.PoincareUncurry` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.Targets.SmoothPurityQbar` | unclaimed | Unchanged signature and exports; no adaptation. |
| `Sheaf.ZetaWeil.WeightPurityRoots` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Concentration` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.DegreeOne` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Exactness` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierWeight` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.LocalDuality` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Perverse` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Purity` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.RealPushforward` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Upper` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.UpperReduction` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.AffineCurve` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.CompactSupport` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.DirectImage` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.FibreCohomology` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.FiniteMap` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.FormalSteps` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.MixedStalk` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.OpenLine` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.RealCurve` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.RealSheaves` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Adic` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Rational` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.FourierTransform.Perverse` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.PoincareDuality.Poincare` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.PoincareDuality.Verdier` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Perverse.Operations` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.SmoothPurity.Defs` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.Statement` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.TraceFormula.Basic` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.Basic` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.CompactCohomology` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.Correspondence` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.Dualizing` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.FixedPoint` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.Frobenius` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.Main` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.Stalk` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.TraceFormula.Statement` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.WeilSheaf.Curve` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.WeilSheaf.CurveEndpoints` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.WeilSheaf.LFunction` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.WeilSheaf.LocalizationRational` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.WeilSheaf.LowerShriekFunctoriality` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.WeilSheaf.RealPurity` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.ZetaFunction.BettiSymmetry` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.ZetaFunction.CohomologicalFamily` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.ZetaFunction.DualityReciprocity` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.ZetaFunction.Examples` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.ZetaFunction.ExamplesCohomology` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.ZetaFunction.FinalTheorems` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.ZetaFunction.HasseWeil` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.ZetaFunction.IntegralFactors` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.ZetaFunction.IntegralFrobeniusFactors` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.ZetaFunction.Rationality` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.ZetaFunction.RealizationIndependence` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.ZetaFunction.RelativePurity` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.ZetaFunction.SmoothProper` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.ZetaFunction.TraceFormula` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.ZetaFunction.WeightSeparation` | unclaimed | Unchanged signature and exports; no adaptation. |
| `WeilConjectures.ZetaFunction.Weights` | unclaimed | Unchanged signature and exports; no adaptation. |

## Status

landed 20261019T034346-L-425219 2026-10-19 (merge of deliver/X5/Sheaf.Paper.OpenImmersionLocalizing)
