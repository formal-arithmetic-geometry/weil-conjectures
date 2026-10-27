# CategoryTheory.ConstantScalarRestriction proof elaboration scope
## Reason

The stage-3 preflight requests a change record because it conservatively flags added
`open`, `variable`, `section`, `universe` and declaration-scoped `attribute` commands.
The new commands elaborate private proved helpers. There is no public signature,
public import, definition body, instance body, visibility or declaration-attribute change.
All existing public definitions remain verbatim.

A new private proof import for the proved native derived-braiding theorem exposes the
high-priority successor-universe sheafification instance. That instance creates stuck
universe constraints at `max u v` while elaborating two existing definitions. Its exclusion
is scoped by `in` to those declarations and restores the prior inference path. It is not
an exported instance-attribute change.

## Old

The affected existing instance declarations were:

```lean
instance fixedSheafify : HasSheafify J (ModuleCat.{max u v} B) :=
  letI : PreservesFilteredColimitsOfSize.{max u v, max u v}
      (CategoryTheory.forget (ModuleCat.{max u v} B)) :=
    ModuleCat.FilteredColimits.forget_preservesFilteredColimits (R := B)
  letI : HasSheafify ((equivSmallModel.{max u v} C).inverse.inducedTopology J)
      (ModuleCat.{max u v} B) :=
    inferInstance
  hasSheafifyEssentiallySmallSite J (ModuleCat.{max u v} B)
```

```lean
instance ringGrothendieck : IsGrothendieckAbelian.{max u v} (Modules J B) :=
  SheafOfModules.isGrothendieckAbelian_coefficientUniverse _
```

There was no `DerivedComparisonProof` section or its private-helper variable/open scope.

## New

The identical instance bodies and signatures are elaborated under the following
single-declaration scope (their declaration attributes are unchanged):

```lean
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
instance fixedSheafify : HasSheafify J (ModuleCat.{max u v} B) :=
  letI : PreservesFilteredColimitsOfSize.{max u v, max u v}
      (CategoryTheory.forget (ModuleCat.{max u v} B)) :=
    ModuleCat.FilteredColimits.forget_preservesFilteredColimits (R := B)
  letI : HasSheafify ((equivSmallModel.{max u v} C).inverse.inducedTopology J)
      (ModuleCat.{max u v} B) :=
    inferInstance
  hasSheafifyEssentiallySmallSite J (ModuleCat.{max u v} B)
```

```lean
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
instance ringGrothendieck : IsGrothendieckAbelian.{max u v} (Modules J B) :=
  SheafOfModules.isGrothendieckAbelian_coefficientUniverse _
```

New helper-only scope:

```lean
section DerivedComparisonProof

set_option backward.isDefEq.respectTransparency false
open CategoryTheory.Category CategoryTheory.Functor CategoryTheory.Functor.LaxMonoidal
open CategoryTheory.Functor.OplaxMonoidal
```

Its category variables and universe declarations occur only in the new private helper
signatures. `end DerivedComparisonProof` precedes every subsequent original declaration.
The complete Lean patch contains their exact declarations and proofs. The section closes
its elaboration options, variables and opens. None of these commands changes an importer.

## Users

`tools/downstream.py Sheaf.CategoryTheory.ConstantScalarRestrictionTensor --uses
fixedSheafify ringGrothendieck` lists 155 transitive importers; neither affected instance name
is mentioned textually outside the item. Instance synthesis remains available with precisely
the same exported signatures. Every transitive importer is listed below with the current
claim holder. No importer is modified or needs adaptation, and no target statement changes.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.CategoryTheory.ConstantScalarRestrictionTensor` | E1 | Nine proofs filled; only private helper scopes added. |
| `Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteDiscreteCtfOrigin` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteDiscreteCtfRealization` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.DeligneLaumon.QbarCurveDuality` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.AdicProperLocalizingAdjunctionComparison` | F6 | Same public interface; no adaptation. |
| `Sheaf.Paper.AdmissibleVerdierExchange` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.AffineSpaceRationalInduction` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.BrownExceptionalAdjoint` | X2 | Same public interface; no adaptation. |
| `Sheaf.Paper.BrownHypothesesGeneration` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.ChartCounitScalarTransport` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.ClosedAdjointConstructibleYoneda` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.CoefficientTowerShriekInterfaces` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.CohomologicalSmoothEtaleLocality` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.CompletedStalkFrobeniusReduction` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.ContinuousQbarExceptionalPreservation` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.CurveIntermediateExtension` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.EtaleAffineProjectionCoefficientMate` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.EtaleCtfChartDomain` | Q4 | Same public interface; no adaptation. |
| `Sheaf.Paper.EtaleProEtaleAdjunctionTransfer` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.EtaleProEtaleCoefficientCompatibility` | C4 | Same public interface; no adaptation. |
| `Sheaf.Paper.EtaleSumCounitScalar` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.ExceptionalInverseImageExistence` | D3 | Same public interface; no adaptation. |
| `Sheaf.Paper.FiniteAdjointMateCompatibility` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.FiniteCoefficientAdjointComparisons` | M8 | Same public interface; no adaptation. |
| `Sheaf.Paper.FiniteCompactSupportDomains` | D4 | Same public interface; no adaptation. |
| `Sheaf.Paper.FiniteComparisonLocalizing` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.FiniteComparisonPresentation` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.FiniteDncNormalizationReduction` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.FiniteFreeCoefficientExtension` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.FiniteFreeCompactComposition` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.FiniteFreeCompactScalar` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.FiniteFreeCompactSupportComposition` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.FiniteFreeComparisonIsomorphismNaturality` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.FiniteFreeProjectionExchange` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.FiniteFreeScalarProjection` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.FiniteLocalizingExceptionalPreservation` | J6 | Same public interface; no adaptation. |
| `Sheaf.Paper.FiniteTorStability` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.FiniteUniversalSmoothTrace` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.FixedStalkIdentificationReduction` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.GlobalVerdierDuality` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.HomChainPairingNaturality` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.IntegralAmbientCoefficientPresentation` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.IntegralAmbientDirectImageEncoding` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.IntegralAmbientTowerComparison` | K7 | Same public interface; no adaptation. |
| `Sheaf.Paper.IntegralCoefficientModelRealization` | Q6 | Same public interface; no adaptation. |
| `Sheaf.Paper.IntegralDirectImageTower` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.LocalizingExceptionalAdjoint` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.LocalizingLowerShriekComposition` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.MateOpenRestriction` | P1 | Same public interface; no adaptation. |
| `Sheaf.Paper.NonrationalCompositionSeed` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.NonrationalLocalizingLowerShriekComposition` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.OpenProEtaleCounitScalar` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.OpenScalarFlatModelRealization` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.OpenScalarSiteCoherence` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.OrderedCompactificationScalarSquare` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.P1CounitScalar` | U3 | Same public interface; no adaptation. |
| `Sheaf.Paper.P1SplittingScalar` | V1 | Same public interface; no adaptation. |
| `Sheaf.Paper.PodCtfAdjunctions` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.PodCtfPairingMaps` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.PodHomChainCounitFormula` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.PodHomChainUncurriedTransport` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.ProjectionFiniteReduction` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.ProperExceptionalRestriction` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.QbarPerverseSubcategories` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.QbarPerverseSupportCondition` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.RationalExceptionalRestriction` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.RationalHomScalarTranspose` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.RationalRestrictionGlue` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.RationalScalarTransposeCompatibility` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.RationalTensorSymmetry` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.RationalVerdierEvaluationAdjoints` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.RestrictionLocal` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.ScalarExchangeConstituents` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.SfBidualityClass` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.SitePerfectRationalBidual` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.SmoothPullbackSupportDimension` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.TateTwistSupportCondition` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.TensorAdjunctionExchange` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.TraceFormulaDualizingComplex` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.TraceFormulaTopologicalInvariance` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.VaryingRingGraphSummand` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.VectorTraceScalarDescent` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.VerdierCoefficientRealization` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Paper.VerdierExchange` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.SecSmoothPurity.ChartFiniteRingAdjunction` | W4 | Same public interface; no adaptation. |
| `Sheaf.SecSmoothPurity.FiniteGeneralRing` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.SecSmoothPurity.MixedBaseChange` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.SecSmoothPurity.OpenScalarRestrictedTransposeExpansion` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.SecSmoothPurity.PurityDncCoefficientTransport` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.SecSmoothPurity.ReductionCompatibilities` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.SecSmoothPurity.ReductionDirectImage` | E4 | Same public interface; no adaptation. |
| `Sheaf.SecSmoothPurity.ReductionExceptional` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.SecSmoothPurity.RestrictionTransitionTranspose` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.SixFunctors.CoefDualFormulaScalarTranspose` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtension` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.SixFunctors.CoefQbarVerdier` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.SixFunctors.CoefTowerEvaluationPairing` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.SixFunctors.CoefTowerNaturalCurrying` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.SixFunctors.CoefTowerTraceRectification` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.SixFunctors.CoefVerdierWeilEquivariance` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.SixFunctors.CtfStabilityDirectImages` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.SixFunctors.FiniteAdjunctionSystemData` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.SixFunctors.FiniteAdjunctionTransition` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.SixFunctors.FiniteCoefficientVerdier` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.SixFunctors.FiniteCompactProetale` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.SixFunctors.FiniteDualizing` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.SixFunctors.FiniteExceptional` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.SixFunctors.FiniteMappingAdjunction` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.SixFunctors.IntegralBrownAdjoint` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.SixFunctors.IntegralComplementFiniteness` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.SixFunctors.IntegralDualizing` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.SixFunctors.IntegralExceptionalAffineChart` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.SixFunctors.IntegralExceptionalAffineFactorization` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.SixFunctors.IntegralExceptionalRestriction` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.SixFunctors.IntegralLocalizingCompactSupport` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionBoundedDescent` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionChartCover` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionClosed` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionGlue` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionLine` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.SixFunctors.IntegralVerdier` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.SixFunctors.NormalizedTowerTensorEvaluation` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.SixFunctors.RationalOperations` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.SixFunctors.RationalRetractEvaluation` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.SixFunctors.RationalVerdier` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.SixFunctorsBasics.BrownHypotheses` | M8 | Same public interface; no adaptation. |
| `Sheaf.SixFunctorsBasics.BrownHypothesesFiniteFieldCompactness` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.SmoothPurity.NormalizedWitness` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Targets.AffineSpaceRationalLine` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Targets.PoincareUncurry` | unclaimed | Same public interface; no adaptation. |
| `Sheaf.Targets.SmoothPurityQbar` | unclaimed | Same public interface; no adaptation. |
| `TargetsCheck` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.PoincareDuality.Poincare` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.PoincareDuality.Verdier` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.SmoothPurity.Defs` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.TraceFormula.Basic` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.Basic` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.CompactCohomology` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.Correspondence` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.Dualizing` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.FixedPoint` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.Frobenius` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.Main` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.Stalk` | unclaimed | Same public interface; no adaptation. |
| `WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek` | unclaimed | Same public interface; no adaptation. |

The five direct importers are `Sheaf.Paper.OpenScalarFlatModelRealization`,
`Sheaf.Paper.IntegralAmbientTowerComparison`, `Sheaf.Paper.IntegralCoefficientModelRealization`,
`Sheaf.Paper.FiniteComparisonPresentation`, and
`Sheaf.Paper.IntegralAmbientCoefficientPresentation`.

Four direct consumers compile unchanged against the patch: `OpenScalarFlatModelRealization`
(21.0 s), `IntegralAmbientTowerComparison` (6.5 s), `IntegralCoefficientModelRealization`
(15.0 s), and `IntegralAmbientCoefficientPresentation` (31.6 s).
`FiniteComparisonPresentation` times out at 60 seconds both against this patch and against
the original unmodified item, after recompiling the baseline item successfully (19.3 s).
That timeout is therefore also reproducible without this delivery. No adaptation is made.
The delivery version was restored after the baseline comparison and compiled again in
33.4 seconds with no warnings.

## Status

landed 20261022T202014-L-1249137 2026-10-22 (merge of deliver/E1/Sheaf.CategoryTheory.ConstantScalarRestrictionTensor)
