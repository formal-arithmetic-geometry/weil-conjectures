# CategoryTheory.Functor.hasLeftDerivedFunctor_of_preservesTotalTensorKFlatQuasiIso

## Reason

Server preflight requires a change record for the added `attribute` commands.
They mark proved private helpers as instances **locally in this module**. They are
not exported as global instances, and no public signature, definition, public import,
universe, or target statement changes. The helpers supply countable coproduct
preservation and the graded tensor coherence hypotheses needed to use the existing
source K-flat machinery. The additive-functor preservation bridge is also local.

A declaration-scoped unused-section-variable linter option retains the existing
`HasDerivedCategory C` hypothesis of the existence theorem; its proof does not need
that hypothesis. Other elaboration options are scoped to the private countable
coproduct helper. No file-wide option changes. Scoped `omit` commands restrict only the private helper
parameters; the original public variable block and public parameters remain unchanged.

## Old

There were no local proof-instance attribute commands in this module. The existing
existence theorem signature and body were, verbatim:

```lean
theorem hasLeftDerivedFunctor_of_preservesTotalTensorKFlatQuasiIso :
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) := by
  sorry
```

## New

The following commands occur after their proved private helper declarations:

```lean
attribute [local instance] preservesCountableTensorLeft preservesCountableTensorRight
attribute [local instance] hasTensorFour hasGoodTensorLeft hasGoodTensorRight
attribute [local instance] preservesKFlatQuasiIso
```

The signature is unchanged and the new proof is:

```lean
theorem hasLeftDerivedFunctor_of_preservesTotalTensorKFlatQuasiIso :
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) := by
  exact F.derives_kFlat.hasLeftDerivedFunctor
```

The original context directive remains verbatim, now preceded by:

```lean
set_option linter.unusedSectionVars false in
```

All seven existing public declarations retain their original signatures. Both
noncomputable definitions retain their original bodies verbatim. The five theorem
bodies are now complete proofs. There are no consumer edits or forced adaptations.
No target-meaning review is reopened, since definitions and signatures did not change.

## Users

`tools/downstream.py` finds the following transitive importers. Its `--uses` scan
finds a public-declaration consumer only in `LeftDerivedTotalTensorExact`, in addition
to the item itself. The direct importers `LocallyFreeDerivedScalars` and
`FlatSingleScalarConventions` mention none of the seven public declaration names.
All three direct importers were read: their statements and construction bodies use
the original interfaces, so these local proof attributes cannot change their meanings.
All three unchanged direct importers compiled individually against the new module
via `lcompile.py --all` (2.6, 1.9, and 8.0 seconds respectively); their temporary
identical sandbox copies were then removed. No consumer changes are delivered.
No transitive importer sees any of the local instance registrations.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.CategoryTheory.DerivedCategory.LeftDerivedTotalTensor` | A7 | Interface unchanged; item proof instances local. |
| `Sheaf.Algebra.Homology.LocallyFreeDerivedScalars` | U2 | Interface unchanged; item proof instances local. |
| `Sheaf.AlgebraicGeometry.ConstructibleCoconeAmbientRealization` | S2 | Interface unchanged; item proof instances local. |
| `Sheaf.AlgebraicGeometry.ConstructibleExactScalarTriangulation` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose` | C5 | Interface unchanged; item proof instances local. |
| `Sheaf.AlgebraicGeometry.IntegralDerivedExtensionComparison` | V6 | Interface unchanged; item proof instances local. |
| `Sheaf.AlgebraicGeometry.ProperHeartBoundRational` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.CategoryTheory.DerivedCategory.LeftDerivedTotalTensorExact` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.DeligneLaumon.QbarCurveDuality` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.AdmissibleVerdierExchange` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.AffineSpaceRationalInduction` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.BrownExceptionalAdjoint` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.ClosedAdjointConstructibleYoneda` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.CoefficientTowerGeometricComposition` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.CoefficientTowerSectionCoordinates` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.CoefficientTowerShriekCalculus` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.CoefficientTowerShriekInterfaces` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.CoefficientTowerTransitionCompatibility` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.CohomologicalSmoothEtaleLocality` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.CompactificationCoherenceCocycle` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.CompactificationLocalizing` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.CompactificationRefinementIdentity` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.CompactificationRefinementLocalizing` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.CompletedStalkFrobeniusReduction` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.ContinuousAlgClProperFiniteness` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.ContinuousAlgClProperHeartFiniteness` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.ContinuousAlgClProperLowerTail` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.ContinuousQbarExceptionalPreservation` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.CurveIntermediateExtension` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.DerivedExchangeExactNormalization` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.DerivedTruncationCoproducts` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.EtaleProEtaleAdjunctionTransfer` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.EtaleProEtaleCoefficientCompatibility` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.ExceptionalInverseImageExistence` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.FiniteCoefficientAdjointComparisons` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.FiniteFreeCoefficientExtension` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.FiniteFreeCompactComposition` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.FiniteFreeCompactScalar` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.FiniteFreeCompactSupportComposition` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.FiniteFreeProjectionExchange` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.FiniteFreeScalarProjection` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.FiniteLocalizingExceptionalPreservation` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.FiniteTorStability` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.FixedStalkIdentificationReduction` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.FlatSingleScalarConventions` | W5 | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.GlobalVerdierDuality` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.IntegralDirectImageTower` | M2 | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.IntegralLocalizingProperBaseChange` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.IntegralOpenImageProperFormulas` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.IntegralProperCohomologicalBounds` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.IntegralProperDirectSums` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.IntegralProperProjectionFormula` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.InterchangeProperPasting` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.LocalizingExceptionalAdjoint` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.LocalizingLowerShriekComposition` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.LocalizingLowerShriekCompositionModel` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.MateOpenRestriction` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.NonrationalCompositionSeed` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.NonrationalLocalizingLowerShriekComposition` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.ProEtaleProjectionExchangeMaps` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.ProEtaleProperOpenInterchange` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.ProjectionFiniteReduction` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.ProperExceptionalRestriction` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.ProperHeartBound` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.ProperHeartBoundReduction` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.ProperIndConstructibleBoundedBelow` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.ProperIndConstructibleUnbounded` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.ProperLocalizingAdmissibleCoefficients` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.ProperLocalizingContinuousAlgCl` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.ProperUnboundedCoproductComparison` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.ProperUnboundedCoproducts` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.ProperUnboundedWindow` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.ProperUnboundedWindowIso` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.QbarPerverseSubcategories` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.QbarPerverseSupportCondition` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.RationalExceptionalRestriction` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.RationalHomScalarTranspose` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.RationalLocalizingProjectionFormula` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.RationalRestrictionGlue` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.RationalScalarTransposeCompatibility` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.RationalTensorSymmetry` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.RationalVerdierEvaluationAdjoints` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.RestrictionLocal` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.ScalarExchangeConstituents` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.SfBidualityClass` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.SitePerfectRationalBidual` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.SmoothPullbackSupportDimension` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.TateTwistSupportCondition` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.TensorAdjunctionExchange` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.TraceBaseChangeSecond` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.TraceFormulaDualizingComplex` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.TraceFormulaTopologicalInvariance` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.UnboundedBaseChangeExtension` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.VaryingRingGraphSummand` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Paper.VerdierExchange` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.SecSmoothPurity.MixedBaseChange` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.SecSmoothPurity.PurityDncCoefficientTransport` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.SecSmoothPurity.ReductionDirectImage` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.SecSmoothPurity.ReductionExceptional` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.SecSmoothPurity.RestrictionTransitionTranspose` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.SixFunctors.CoefDualFormulaScalarTranspose` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtension` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.SixFunctors.CoefQbarVerdier` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.SixFunctors.CoefTowerEvaluationPairing` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.SixFunctors.CoefTowerNaturalCurrying` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.SixFunctors.CoefTowerTraceRectification` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.SixFunctors.CoefVerdierWeilEquivariance` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.SixFunctors.CtfStabilityDirectImages` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.SixFunctors.DetSfCompCompositionBaseChange` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.SixFunctors.FiniteAdjunctionSystemData` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.SixFunctors.FiniteAdjunctionTransition` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.SixFunctors.FiniteCoefficientVerdier` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.SixFunctors.FiniteDualizing` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.SixFunctors.FiniteExceptional` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.SixFunctors.FiniteMappingAdjunction` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.SixFunctors.IntegralBrownAdjoint` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.SixFunctors.IntegralComplementFiniteness` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.SixFunctors.IntegralDualizing` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.SixFunctors.IntegralExceptionalAffineChart` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.SixFunctors.IntegralExceptionalAffineFactorization` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.SixFunctors.IntegralExceptionalRestriction` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.SixFunctors.IntegralLocalizingCompactSupport` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.SixFunctors.IntegralRestrictionBoundedDescent` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.SixFunctors.IntegralRestrictionChartCover` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.SixFunctors.IntegralRestrictionClosed` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.SixFunctors.IntegralRestrictionGlue` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.SixFunctors.IntegralRestrictionLine` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.SixFunctors.IntegralVerdier` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.SixFunctors.NormalizedTowerTensorEvaluation` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.SixFunctors.ProperImageLocalizingProper` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.SixFunctors.RationalOperations` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.SixFunctors.RationalRetractEvaluation` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.SixFunctors.RationalVerdier` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.SmoothPurity.NormalizedWitness` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Targets.AffineSpaceRationalLine` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Targets.PoincareUncurry` | unclaimed | Interface unchanged; item proof instances local. |
| `Sheaf.Targets.SmoothPurityQbar` | unclaimed | Interface unchanged; item proof instances local. |
| `TargetsCheck` | unclaimed | Interface unchanged; item proof instances local. |
| `WeilConjectures` | unclaimed | Interface unchanged; item proof instances local. |
| `WeilConjectures.PoincareDuality.Poincare` | unclaimed | Interface unchanged; item proof instances local. |
| `WeilConjectures.PoincareDuality.Verdier` | unclaimed | Interface unchanged; item proof instances local. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition` | unclaimed | Interface unchanged; item proof instances local. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek` | unclaimed | Interface unchanged; item proof instances local. |
| `WeilConjectures.SmoothPurity.Defs` | unclaimed | Interface unchanged; item proof instances local. |
| `WeilConjectures.TraceFormula.Basic` | unclaimed | Interface unchanged; item proof instances local. |
| `WeilConjectures.TraceFormula.CompactCohomology` | unclaimed | Interface unchanged; item proof instances local. |
| `WeilConjectures.TraceFormula.Correspondence` | unclaimed | Interface unchanged; item proof instances local. |
| `WeilConjectures.TraceFormula.Dualizing` | unclaimed | Interface unchanged; item proof instances local. |
| `WeilConjectures.TraceFormula.FixedPoint` | unclaimed | Interface unchanged; item proof instances local. |
| `WeilConjectures.TraceFormula.Frobenius` | unclaimed | Interface unchanged; item proof instances local. |
| `WeilConjectures.TraceFormula.Main` | unclaimed | Interface unchanged; item proof instances local. |
| `WeilConjectures.TraceFormula.Slop.Basic` | unclaimed | Interface unchanged; item proof instances local. |
| `WeilConjectures.TraceFormula.Slop.CompactCohomology` | unclaimed | Interface unchanged; item proof instances local. |
| `WeilConjectures.TraceFormula.Slop.Correspondence` | unclaimed | Interface unchanged; item proof instances local. |
| `WeilConjectures.TraceFormula.Slop.Dualizing` | unclaimed | Interface unchanged; item proof instances local. |
| `WeilConjectures.TraceFormula.Slop.FixedPoint` | unclaimed | Interface unchanged; item proof instances local. |
| `WeilConjectures.TraceFormula.Slop.Frobenius` | unclaimed | Interface unchanged; item proof instances local. |
| `WeilConjectures.TraceFormula.Slop.Main` | unclaimed | Interface unchanged; item proof instances local. |
| `WeilConjectures.TraceFormula.Slop.Stalk` | unclaimed | Interface unchanged; item proof instances local. |
| `WeilConjectures.TraceFormula.Stalk` | unclaimed | Interface unchanged; item proof instances local. |
| `WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek` | unclaimed | Interface unchanged; item proof instances local. |

## Status

landed 20261021T110920-L-3801136 2026-10-21 (merge of deliver/A7/Sheaf.CategoryTheory.DerivedCategory.LeftDerivedTotalTensor)
