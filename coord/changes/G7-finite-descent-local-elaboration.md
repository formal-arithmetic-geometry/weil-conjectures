# AlgebraicGeometry.ProEtale.finiteCoefficientDescentTwoColimit

## Reason

The completed proof compares canonical derived scalar maps and zero-shift maps.
Local irreducibility prevents elaboration from unfolding the large derived-functor
constructions while checking those interfaces. Private helpers also use scoped
`open ... in` commands. The static interface check conservatively flags these new
commands, so this record documents their scope and consumers.

The three original public definitions, every public signature, all four public
imports, and the existing namespace/open/universe commands are unchanged. All added
helper lemmas are private and proved. Both attribute commands say `local`; they
expire at the end of this file's namespace and add no persistent attribute to
any imported declaration. The heartbeat option applies only to the theorem.
No downstream statement changes meaning and no consumer adaptation is needed.

## Old

No local irreducibility attributes or declaration-local heartbeat option.
The original three definition bodies and theorem signature are retained verbatim.
The theorem proof was `by sorry`.

## New

```lean
attribute [local irreducible] Functor.leftDerivedFunctorIsoMapDerivedCategory
  Functor.CommShift.ofIso Functor.leftDerivedFunctor Functor.mapDerivedCategory

attribute [local irreducible] finiteCoefficientDerivedHomEquiv finiteCoefficientDerivedAlgClHomEquiv
  finiteDescentDerivedHomToAlgCl finiteDescentDerivedHomTransition
  coefficientDescentHomToAlgCl coefficientDescentHomTransition

set_option maxHeartbeats 800000 in
```

The heartbeat option governs the existing theorem, whose proof is now complete.
The only new `open ... in` commands govern individual private helpers:

```lean
open MonoidalCategory MonObj Functor.LaxMonoidal Functor.OplaxMonoidal in
open MonoidalCategory MonObj in
```

## Users

The table includes all transitive importers reported by `tools/downstream.py`,
as well as the item. Holders are read from the coordination claims at preparation
time. No module other than the item is delivered or adapted. Textual search for
`finiteCoefficientDescentTwoColimit` finds only its declaration in the item;
all downstream effects below are unchanged exported signatures and definitions.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded` | X2 | exported interface unchanged; no adaptation |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology` | C8 | exported interface unchanged; no adaptation |
| `Sheaf.AlgebraicGeometry.EllAdicProperLocalizingCoproducts` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound` | D4 | exported interface unchanged; no adaptation |
| `Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.AlgebraicGeometry.ProperHeartBoundRational` | W8 | exported interface unchanged; no adaptation |
| `Sheaf.DeligneLaumon.Reduction.AffineCurveUpper` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.DeligneLaumon.Reduction.Composition` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.Paper.AdicPurityExceptionalReduction` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.Paper.AdicPurityFiniteTensor` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.Paper.AdicPurityObjects` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.Paper.AdicPurityRootComparisons` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.Paper.AdicPuritySourceReduction` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.Paper.AdicPurityTwistReduction` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.Paper.AdicSmoothDualizingComplexes` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.Paper.AffineSpaceRationalInduction` | Q2 | exported interface unchanged; no adaptation |
| `Sheaf.Paper.ArithmeticRoots` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.Paper.BoundedConstructibleHomFiniteness` | H5 | exported interface unchanged; no adaptation |
| `Sheaf.Paper.BrownExceptionalAdjoint` | T6 | exported interface unchanged; no adaptation |
| `Sheaf.Paper.BrownHypothesesGeneration` | E1 | exported interface unchanged; no adaptation |
| `Sheaf.Paper.ClosedAdjointConstructibleYoneda` | M1 | exported interface unchanged; no adaptation |
| `Sheaf.Paper.CoefficientTowerShriekCalculus` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.Paper.CohomologicalSmoothEtaleLocality` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.Paper.CommonStageConstituentNonexceptional` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.Paper.CommonStageFourierWeightUpper` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.Paper.CompactificationCoherenceCocycle` | R4 | exported interface unchanged; no adaptation |
| `Sheaf.Paper.CompactificationLocalizing` | F4 | exported interface unchanged; no adaptation |
| `Sheaf.Paper.CompactificationRefinementLocalizing` | T9 | exported interface unchanged; no adaptation |
| `Sheaf.Paper.ConstructibleCompactness` | U7 | exported interface unchanged; no adaptation |
| `Sheaf.Paper.ConstructibleFiniteTorAdjunctions` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.Paper.CurveIntermediateExtension` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.Paper.CurveMiddleExtensionUpper` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.Paper.DetThmSfCtfStabilityInternalHom` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.Paper.DualizingObjectPurity` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.Paper.EtaleProEtaleAdjunctionTransfer` | V5 | exported interface unchanged; no adaptation |
| `Sheaf.Paper.EtaleProEtaleCoefficientCompatibility` | Y8 | exported interface unchanged; no adaptation |
| `Sheaf.Paper.ExceptionalInverseImageExistence` | U1 | exported interface unchanged; no adaptation |
| `Sheaf.Paper.ExtensionByZeroPunctual` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.Paper.FiniteCoefficientAdjointComparisons` | U2 | exported interface unchanged; no adaptation |
| `Sheaf.Paper.FiniteCoefficientDescentTwoColimit` | G7 | proof completed; local elaboration attributes |
| `Sheaf.Paper.FiniteCoefficientSmoothPurity` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.Paper.FiniteLocalizingExceptionalPreservation` | Q7 | exported interface unchanged; no adaptation |
| `Sheaf.Paper.FiniteReductionAffineOrientation` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.Paper.FiniteReductionChartCalculus` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.Paper.FiniteReductionComparisons` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.Paper.FiniteReductionOfPurity` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.Paper.FiniteReductionRootCharts` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.Paper.FiniteSmoothPullbackExchange` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.Paper.FiniteTorStability` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.Paper.FiniteWindow` | W5 | exported interface unchanged; no adaptation |
| `Sheaf.Paper.FiniteWindowBounded` | C1 | exported interface unchanged; no adaptation |
| `Sheaf.Paper.FiniteWindowUnbounded` | C7 | exported interface unchanged; no adaptation |
| `Sheaf.Paper.FourierTraceFormula` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.Paper.IndHeartIIVanishing` | E9 | exported interface unchanged; no adaptation |
| `Sheaf.Paper.IntegralDirectImageTower` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.Paper.IntegralLocalizingProperBaseChange` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.Paper.IntegralOpenImageProperFormulas` | R8 | exported interface unchanged; no adaptation |
| `Sheaf.Paper.IntegralProperProjectionFormula` | W9 | exported interface unchanged; no adaptation |
| `Sheaf.Paper.InterchangeProperPasting` | S4 | exported interface unchanged; no adaptation |
| `Sheaf.Paper.LocalizingExceptionalAdjoint` | J5 | exported interface unchanged; no adaptation |
| `Sheaf.Paper.LocalizingLowerShriekComposition` | A4 | exported interface unchanged; no adaptation |
| `Sheaf.Paper.MateOpenRestriction` | D7 | exported interface unchanged; no adaptation |
| `Sheaf.Paper.ModelCompactComparisonUnit` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.Paper.NonrationalLocalizingLowerShriekComposition` | B3 | exported interface unchanged; no adaptation |
| `Sheaf.Paper.ProEtaleProjectionExchangeMaps` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.Paper.ProEtaleProperOpenInterchange` | X6 | exported interface unchanged; no adaptation |
| `Sheaf.Paper.ProperExceptionalRestriction` | P2 | exported interface unchanged; no adaptation |
| `Sheaf.Paper.ProperHeartBound` | K5 | exported interface unchanged; no adaptation |
| `Sheaf.Paper.ProperHeartBoundReduction` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.Paper.ProperIndConstructibleBoundedBelow` | Q3 | exported interface unchanged; no adaptation |
| `Sheaf.Paper.ProperIndConstructibleUnbounded` | K6 | exported interface unchanged; no adaptation |
| `Sheaf.Paper.ProperUnboundedCoproducts` | U2 | exported interface unchanged; no adaptation |
| `Sheaf.Paper.ProperUnboundedWindow` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.Paper.ProperUnboundedWindowIso` | F8 | exported interface unchanged; no adaptation |
| `Sheaf.Paper.PurAdicReconstruction` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.Paper.PurityCompositionCoherence` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.Paper.PurityDiagonalDualizingObject` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.Paper.PurityDncInvariance` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.Paper.QbarPerverseSubcategories` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.Paper.QbarPerverseSupportCondition` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.Paper.QuasiFiniteCompactSupportWeights` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.Paper.RationalExceptionalRestriction` | K8 | exported interface unchanged; no adaptation |
| `Sheaf.Paper.RationalLocalizingProjectionFormula` | U4 | exported interface unchanged; no adaptation |
| `Sheaf.Paper.RationalPurityPresentation` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.Paper.RationalRestrictionGlue` | R9 | exported interface unchanged; no adaptation |
| `Sheaf.Paper.RegularImmersionPurityComparison` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.Paper.RestrictionLocal` | R3 | exported interface unchanged; no adaptation |
| `Sheaf.Paper.SfBidualityClass` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.Paper.SmoothPullbackSupportDimension` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.Paper.SmoothPurityMap` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.Paper.SmoothTrace` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.Paper.TateTwistSupportCondition` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.Paper.TraceBaseChangeSecond` | E4 | exported interface unchanged; no adaptation |
| `Sheaf.Paper.TraceFormulaDualizingComplex` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.Paper.TraceFormulaTopologicalInvariance` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.Paper.UnboundedBaseChangeExtension` | K3 | exported interface unchanged; no adaptation |
| `Sheaf.Paper.UniformConstructibleExt` | X9 | exported interface unchanged; no adaptation |
| `Sheaf.Paper.UniformConstructibleExtRational` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.Paper.VaryingRingGraphSummand` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.Paper.VerdierExchange` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.Paper.WeilFourierInversion` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.Paper.WeilFourierPlancherel` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.Paper.WeilOne` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.Paper.ZlShriekComposition` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.SecSmoothPurity.FiniteGeneralRing` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.SecSmoothPurity.MixedBaseChange` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.SecSmoothPurity.ReductionDirectImage` | F1 | exported interface unchanged; no adaptation |
| `Sheaf.SecSmoothPurity.ReductionExceptional` | F3 | exported interface unchanged; no adaptation |
| `Sheaf.SecSmoothPurity.RestrictionTransitionTranspose` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.SecSmoothPurity.SmoothPurityNaturality` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.SixFunctors.CoefDualFormulaScalarTranspose` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtension` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.SixFunctors.CoefQbarVerdier` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.SixFunctors.CoefTowerEvaluationPairing` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.SixFunctors.CoefTowerTraceRectification` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.SixFunctors.CtfStabilityDirectImages` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.SixFunctors.DetSfCompCompositionBaseChange` | H6 | exported interface unchanged; no adaptation |
| `Sheaf.SixFunctors.FiniteCoefficientVerdier` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.SixFunctors.FiniteDualizing` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.SixFunctors.IntegralBrownAdjoint` | M7 | exported interface unchanged; no adaptation |
| `Sheaf.SixFunctors.IntegralDualizing` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.SixFunctors.IntegralExceptionalRestriction` | N4 | exported interface unchanged; no adaptation |
| `Sheaf.SixFunctors.IntegralLocalizingCompactSupport` | T2 | exported interface unchanged; no adaptation |
| `Sheaf.SixFunctors.IntegralRestrictionClosed` | U3 | exported interface unchanged; no adaptation |
| `Sheaf.SixFunctors.IntegralRestrictionGlue` | G9 | exported interface unchanged; no adaptation |
| `Sheaf.SixFunctors.IntegralRestrictionLine` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.SixFunctors.IntegralVerdier` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.SixFunctors.ProperImageLocalizingProper` | B4 | exported interface unchanged; no adaptation |
| `Sheaf.SixFunctors.RationalOperations` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.SixFunctors.RationalVerdier` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.SixFunctorsBasics.BrownHypotheses` | U1 | exported interface unchanged; no adaptation |
| `Sheaf.SmoothPurity.NormalizedWitness` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.Targets.AffineSpaceRationalLine` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.Targets.PoincareUncurry` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.Targets.SmoothPurityQbar` | unclaimed | exported interface unchanged; no adaptation |
| `Sheaf.ZetaWeil.WeightPurityRoots` | unclaimed | exported interface unchanged; no adaptation |
| `TargetsCheck` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.DeligneLaumon.AffineLine.Concentration` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.DeligneLaumon.AffineLine.DegreeOne` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.DeligneLaumon.AffineLine.Exactness` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierWeight` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.DeligneLaumon.AffineLine.LocalDuality` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.DeligneLaumon.AffineLine.Perverse` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.DeligneLaumon.AffineLine.Purity` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.DeligneLaumon.AffineLine.RealPushforward` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.DeligneLaumon.AffineLine.Upper` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.DeligneLaumon.AffineLine.UpperReduction` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.DeligneLaumon.Reduction.AffineCurve` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.DeligneLaumon.Reduction.CompactSupport` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.DeligneLaumon.Reduction.DirectImage` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.DeligneLaumon.Reduction.FibreCohomology` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.DeligneLaumon.Reduction.FiniteMap` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.DeligneLaumon.Reduction.FormalSteps` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.DeligneLaumon.Reduction.MixedStalk` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.DeligneLaumon.Reduction.OpenLine` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.DeligneLaumon.Reduction.RealCurve` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.DeligneLaumon.Reduction.RealSheaves` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Adic` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Rational` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.FourierTransform.Perverse` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.PoincareDuality.Poincare` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.PoincareDuality.Verdier` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.SixFunctors.Etale.Perverse.Operations` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.SmoothPurity.Defs` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.Statement` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.TraceFormula.Basic` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.TraceFormula.Slop.Basic` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.TraceFormula.Slop.CompactCohomology` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.TraceFormula.Slop.Correspondence` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.TraceFormula.Slop.Dualizing` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.TraceFormula.Slop.FixedPoint` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.TraceFormula.Slop.Frobenius` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.TraceFormula.Slop.Main` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.TraceFormula.Slop.Stalk` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.TraceFormula.Statement` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.WeilSheaf.Curve` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.WeilSheaf.CurveEndpoints` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.WeilSheaf.LFunction` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.WeilSheaf.LocalizationRational` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.WeilSheaf.LowerShriekFunctoriality` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.WeilSheaf.RealPurity` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.ZetaFunction.BettiSymmetry` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.ZetaFunction.CohomologicalFamily` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.ZetaFunction.DualityReciprocity` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.ZetaFunction.Examples` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.ZetaFunction.ExamplesCohomology` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.ZetaFunction.FinalTheorems` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.ZetaFunction.HasseWeil` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.ZetaFunction.IntegralFactors` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.ZetaFunction.IntegralFrobeniusFactors` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.ZetaFunction.Rationality` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.ZetaFunction.RealizationIndependence` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.ZetaFunction.RelativePurity` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.ZetaFunction.SmoothProper` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.ZetaFunction.TraceFormula` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.ZetaFunction.WeightSeparation` | unclaimed | exported interface unchanged; no adaptation |
| `WeilConjectures.ZetaFunction.Weights` | unclaimed | exported interface unchanged; no adaptation |

## Status

landed 20261019T005301-L-2748077 2026-10-19 (merge of deliver/G7/Sheaf.Paper.FiniteCoefficientDescentTwoColimit)
