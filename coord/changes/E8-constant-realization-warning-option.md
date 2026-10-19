# AlgebraicGeometry.ProEtale.constantRealization_detects_zero

## Reason

Repair returned delivery `5e239ad9f`. The source hole scanner treated the `sorry`
component of the unnecessary `warn.sorry` option as an unattributed hole at line 21.
Remove that option. The theorem is fully proved; the default warnings can remain enabled.
The preflight conservatively classifies removal of a file-level option as an interface
change, so this record accounts for it. No signature, definition, public import or target
statement changes. Lean options apply to this file and are not exported to importers.

## Old

```lean
set_option autoImplicit false
set_option warn.sorry false
```

## New

```lean
set_option autoImplicit false
```

## Users

The source-only downstream scan found the following modules. Only the assigned module
is edited. Its consumers see the same declaration types and definition body; warning
configuration is local to each source file. The direct theorem consumer is
`Sheaf.CategoryTheory.ConstantRealizationReflectsIsomorphism`; the other direct importer
is `Sheaf.Paper.WContractibleConstantReductionsML`. No consumer adaptation is needed.
The full transitive downstream inventory is recorded below, with holders read at repair.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded` | X2 | No semantic or elaboration change; no adaptation. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology` | C8 | No semantic or elaboration change; no adaptation. |
| `Sheaf.AlgebraicGeometry.EllAdicProperLocalizingCoproducts` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound` | D4 | No semantic or elaboration change; no adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.AlgebraicGeometry.IntegralModelsStacks` | H9 | No semantic or elaboration change; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProEtale.ConstantRealizationDetectsZero` | E8 | Remove local warning suppression; proof complete. |
| `Sheaf.CategoryTheory.ConstantRealizationReflectsIsomorphism` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.DeligneLaumon.Reduction.AffineCurveUpper` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.DeligneLaumon.Reduction.Composition` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.AdicExceptionalCoherence` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.AdicExceptionalComposition` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.AdicExceptionalProjection` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.AdicExceptionalScalars` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.AdicPurityExceptionalReduction` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.AdicPurityFiniteTensor` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.AdicPurityObjects` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.AdicPurityRootComparisons` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.AdicPuritySourceReduction` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.AdicPurityTwistReduction` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.AdicResidueLissePerfectLift` | V6 | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.AdicSmoothDualizingComplexes` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.AdicStratifiedPerfect` | P5 | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.AffineSpaceRationalInduction` | Q2 | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.ArithmeticRoots` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.BrownExceptionalAdjoint` | T6 | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.ClosedAdjointConstructibleYoneda` | M1 | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.CoefficientTowerShriekCalculus` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.CohomologicalSmoothEtaleLocality` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.CommonStageConstituentNonexceptional` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.CommonStageFourierWeightUpper` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.CompactificationCoherenceCocycle` | R4 | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.CompactificationLocalizing` | F4 | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.CompactificationRefinementLocalizing` | H3 | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.ConstructibleFiniteTorAdjunctions` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.ContinuousQbarExceptionalPreservation` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.CurveIntermediateExtension` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.CurveMiddleExtensionUpper` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.DetThmSfCtfStabilityInternalHom` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.DualizingObjectPurity` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.EtaleProEtaleAdjunctionTransfer` | V5 | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.EtaleProEtaleCoefficientCompatibility` | Y8 | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.ExceptionalInverseImageExistence` | U1 | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.ExtensionByZeroPunctual` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.FiniteCoefficientAdjointComparisons` | F3 | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.FiniteCoefficientSmoothPurity` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.FiniteLocalizingExceptionalPreservation` | Q7 | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.FiniteReductionAffineOrientation` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.FiniteReductionChartCalculus` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.FiniteReductionComparisons` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.FiniteReductionOfPurity` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.FiniteReductionRootCharts` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.FiniteRegularReductionDualizing` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.FiniteSmoothPullbackExchange` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.FiniteTorStability` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.FixedStalkIdentificationReduction` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.FourierTraceFormula` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.GeneralCondensedWeilRealization` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.IntegralCohomologicalAdicCriterion` | V4 | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.IntegralConstructibleHeart` | P1 | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.IntegralDirectImageTower` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.IntegralHeartDualizable` | C5 | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.IntegralHeartLocalModel` | C3 | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.IntegralLocalizingProperBaseChange` | H2 | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.IntegralModels` | D4 | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.IntegralOpenImageProperFormulas` | R8 | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.IntegralProperDirectSums` | F5 | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.IntegralProperProjectionFormula` | W9 | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.InterchangeProperPasting` | S4 | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.LocalizingExceptionalAdjoint` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.LocalizingLowerShriekComposition` | A4 | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.MateOpenRestriction` | U2 | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.ModelCompactComparisonUnit` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.NonrationalLocalizingLowerShriekComposition` | B3 | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.ProEtaleProjectionExchangeMaps` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.ProEtaleProperOpenInterchange` | X6 | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.ProperExceptionalRestriction` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.PurAdicReconstruction` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.PurityCompositionCoherence` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.PurityDiagonalDualizingObject` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.PurityDncInvariance` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.QbarMiddleTStructure` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.QbarPerverseSubcategories` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.QbarPerverseSupportCondition` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.QuasiFiniteCompactSupportWeights` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.RationalExceptionalRestriction` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.RationalLocalizingProjectionFormula` | U4 | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.RationalPurityPresentation` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.RationalRestrictionGlue` | R9 | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.RationalSmoothPurityCanonical` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.RationalWeilPurityNaturalityMate` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.RegularImmersionPurityComparison` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.RestrictionLocal` | R3 | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.SfBidualityClass` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.SmoothPullbackSupportDimension` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.SmoothPurityMap` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.SmoothTrace` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.TateTwistSupportCondition` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.TraceBaseChangeSecond` | E4 | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.TraceFormulaDualizingComplex` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.TraceFormulaTopologicalInvariance` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.TwistFrobeniusScalar` | G4 | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.UnboundedBaseChangeExtension` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.VaryingRingGraphSummand` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.VerdierExchange` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.WContractibleConstantReductionsML` | Z6 | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.WeilFourierInversion` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.WeilFourierPlancherel` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.WeilOne` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Paper.ZlShriekComposition` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.SecSmoothPurity.FiniteGeneralRing` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.SecSmoothPurity.MixedBaseChange` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.SecSmoothPurity.PurityDncCoefficientTransport` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.SecSmoothPurity.ReductionCompatibilities` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.SecSmoothPurity.ReductionDirectImage` | F1 | No semantic or elaboration change; no adaptation. |
| `Sheaf.SecSmoothPurity.ReductionExceptional` | G8 | No semantic or elaboration change; no adaptation. |
| `Sheaf.SecSmoothPurity.RestrictionTransitionTranspose` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.SecSmoothPurity.SmoothPurityNaturality` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.SixFunctors.ArbitraryFieldVerdier` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.SixFunctors.CoefDualFormulaScalarTranspose` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtension` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.SixFunctors.CoefQbarVerdier` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.SixFunctors.CoefTowerEvaluationPairing` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.SixFunctors.CoefTowerTraceRectification` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.SixFunctors.CtfStabilityDirectImages` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.SixFunctors.DetSfCompCompositionBaseChange` | H6 | No semantic or elaboration change; no adaptation. |
| `Sheaf.SixFunctors.FiniteCoefficientVerdier` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.SixFunctors.FiniteDualizing` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.SixFunctors.FiniteMappingAdjunction` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.SixFunctors.IntegralBrownAdjoint` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.SixFunctors.IntegralDualizing` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.SixFunctors.IntegralExceptionalAffineChart` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.SixFunctors.IntegralExceptionalAffineFactorization` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.SixFunctors.IntegralExceptionalRestriction` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.SixFunctors.IntegralLocalizingCompactSupport` | T2 | No semantic or elaboration change; no adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionBoundedDescent` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionChartCover` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionClosed` | U3 | No semantic or elaboration change; no adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionGlue` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionLine` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.SixFunctors.IntegralVerdier` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.SixFunctors.ProperImageLocalizingProper` | K2 | No semantic or elaboration change; no adaptation. |
| `Sheaf.SixFunctors.QbarDualRecollement` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.SixFunctors.RationalOperations` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.SixFunctors.RationalVerdier` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.SmoothPurity.NormalizedWitness` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Targets.AffineSpaceRationalLine` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Targets.PoincareUncurry` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.Targets.SmoothPurityQbar` | unclaimed | No semantic or elaboration change; no adaptation. |
| `Sheaf.ZetaWeil.WeightPurityRoots` | unclaimed | No semantic or elaboration change; no adaptation. |
| `TargetsCheck` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Concentration` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.DegreeOne` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Exactness` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierWeight` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.LocalDuality` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Perverse` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Purity` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.RealPushforward` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Upper` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.UpperReduction` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.AffineCurve` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.CompactSupport` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.DirectImage` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.FibreCohomology` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.FiniteMap` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.FormalSteps` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.MixedStalk` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.OpenLine` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.RealCurve` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.RealSheaves` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Adic` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Rational` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.FourierTransform.Perverse` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.PoincareDuality.Poincare` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.PoincareDuality.Verdier` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Perverse.Operations` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.SmoothPurity.Defs` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.Statement` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.TraceFormula.Basic` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.Basic` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.CompactCohomology` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.Correspondence` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.Dualizing` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.FixedPoint` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.Frobenius` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.Main` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.Stalk` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.TraceFormula.Statement` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.WeilSheaf.Curve` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.WeilSheaf.CurveEndpoints` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.WeilSheaf.LFunction` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.WeilSheaf.LocalizationRational` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.WeilSheaf.LowerShriekFunctoriality` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.WeilSheaf.RealPurity` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.ZetaFunction.BettiSymmetry` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.ZetaFunction.CohomologicalFamily` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.ZetaFunction.DualityReciprocity` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.ZetaFunction.Examples` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.ZetaFunction.ExamplesCohomology` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.ZetaFunction.FinalTheorems` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.ZetaFunction.HasseWeil` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.ZetaFunction.IntegralFactors` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.ZetaFunction.IntegralFrobeniusFactors` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.ZetaFunction.Rationality` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.ZetaFunction.RealizationIndependence` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.ZetaFunction.RelativePurity` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.ZetaFunction.SmoothProper` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.ZetaFunction.TraceFormula` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.ZetaFunction.WeightSeparation` | unclaimed | No semantic or elaboration change; no adaptation. |
| `WeilConjectures.ZetaFunction.Weights` | unclaimed | No semantic or elaboration change; no adaptation. |

## Status

landed 20261019T093349-L-2301611 2026-10-19 (merge of deliver/E8/Sheaf.AlgebraicGeometry.ProEtale.ConstantRealizationDetectsZero)
