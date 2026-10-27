# AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectProjectionMap

## Reason

The inferred type of the original projection map repeatedly expands the chosen derived
category, monoidal structures and functor categories while checking coefficient transport.
The complete bounded projection proof exceeded the single-file limit. Store the existing
category, endpoints and canonical mate together in `ProjectionMorphismData`, and expose its
morphism field. This is a construction of the same data, with a compact elaboration
interface; it introduces no choice from an unproved existence theorem.

The original map's binders and two public imports are retained. The new generic record has
its stored category registered as an instance so maps through the record use that exact
category. All fields are filled by the original canonical expression. The new proved
`isIso_moduleObjectProjectionMap_iff` lemma in
`Sheaf.PoincareDuality.ModuleObjectProjectionMorphism` checks this interface against the
abstract adjunction projection, by reflexivity. No mathematical definition or target
meaning changes. Targets depending on this definition may be re-reviewed against this
record and the normalization proof; no target statement is edited.

## Old

```lean
def moduleObjectProjectionMap
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) :=
  (((derivedUpperStarLowerStarAdjunction Λ f).rightAdjointProjectionMap
    (T_C := derivedTensor Λ X) (T_D := derivedTensor Λ Y)
    (leftDerivedUpperStarTensor Λ f)).app K).app L
```

## New

```lean
/-- A morphism together with its category and endpoints, used to keep the projection
map interface compact. All fields below are filled by the existing canonical construction.
Source: the canonical-map convention (blueprint: def-sfb-module-object-projection-map). -/
structure ProjectionMorphismData where
  carrier : Type (v + 1)
  [category : Category.{v} carrier]
  source : carrier
  target : carrier
  morphism : source ⟶ target

attribute [instance 20000] ProjectionMorphismData.category

/-- The existing canonical projection construction, together with its exact category
and endpoints. Source: the canonical-map convention
(blueprint: def-sfb-module-object-projection-map). -/
def moduleObjectProjectionData
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) : ProjectionMorphismData :=
  { carrier := _
    category := _
    source := _
    target := _
    morphism := (((derivedUpperStarLowerStarAdjunction Λ f).rightAdjointProjectionMap
      (T_C := derivedTensor Λ X) (T_D := derivedTensor Λ Y)
      (leftDerivedUpperStarTensor Λ f)).app K).app L }

/-- The canonical projection map: the adjoint transpose of the generic K-flat
pullback tensor comparison followed by counit tensor identity.
Source: blueprint sk-thm-sf-pf-adic-projection; Stacks 0943
(blueprint: def-sfb-module-object-projection-map). -/
def moduleObjectProjectionMap
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) :=
  (moduleObjectProjectionData Λ f K L).morphism
```

## Users

The current `tools/downstream.py Sheaf.Paper.ModuleObjectProjectionMap
--uses moduleObjectProjectionMap` lists 170 downstream modules and eight textual users
(including the defining module). All are listed below. The seven external textual users
and the restored parent `WeilConjectures.PoincareDuality.ProjectionFormula` were submitted
from their unchanged current sources for validation against the repaired definition.
The combined check stopped on a missing published parent artifact in an unpublished
OpenImmersionLocalizing dependency; a separate current parent compile exceeded its file
limit. The four earlier direct-consumer checks are retained in the report. The current
check produced no interface error attributable to the record definition. No consumer source
or signature is adapted. The record unfolds to the original category, endpoints and map;
therefore these consumers' statements keep exactly their previous meaning.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose` | C5 | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.DeligneLaumon.QbarCurveDuality` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.AdmissibleVerdierExchange` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.AffineSpaceRationalInduction` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.BrownExceptionalAdjoint` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.ClosedAdjointConstructibleYoneda` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.CoefficientProjectionSquare` | unclaimed | definitionally the same canonical map; source unchanged |
| `Sheaf.Paper.CoefficientTowerGeometricComposition` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.CoefficientTowerSectionCoordinates` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.CoefficientTowerShriekCalculus` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.CoefficientTowerShriekInterfaces` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.CoefficientTowerTransitionCompatibility` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.CohomologicalSmoothEtaleLocality` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.CompactificationCoherenceCocycle` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.CompactificationLocalizing` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.CompactificationRefinementIdentity` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.CompactificationRefinementLocalizing` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.CompletedStalkFrobeniusReduction` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.ContinuousAlgClProperFiniteness` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.ContinuousAlgClProperHeartFiniteness` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.ContinuousAlgClProperLowerTail` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.ContinuousQbarExceptionalPreservation` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.CurveIntermediateExtension` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.DerivedTruncationCoproducts` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.EtaleProEtaleAdjunctionTransfer` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.EtaleProEtaleCoefficientCompatibility` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.ExceptionalInverseImageExistence` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.FiniteAdjointMateCompatibility` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.FiniteCoefficientAdjointComparisons` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.FiniteDncNormalizationReduction` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.FiniteFreeCoefficientExtension` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.FiniteFreeCompactComposition` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.FiniteFreeCompactScalar` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.FiniteFreeCompactSupportComposition` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.FiniteFreeProjectionExchange` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.FiniteFreeScalarProjection` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.FiniteLocalizingExceptionalPreservation` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.FiniteProperLocalizing` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.FiniteTorStability` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.FiniteUniversalSmoothTrace` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.FixedStalkIdentificationReduction` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.GlobalVerdierDuality` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.IntegralDirectImageTower` | unclaimed | definitionally the same canonical map; source unchanged |
| `Sheaf.Paper.IntegralLocalizingProperBaseChange` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.IntegralOpenImageProperFormulas` | unclaimed | definitionally the same canonical map; source unchanged |
| `Sheaf.Paper.IntegralProperBaseChange` | unclaimed | definitionally the same canonical map; source unchanged |
| `Sheaf.Paper.IntegralProperCohomologicalBounds` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.IntegralProperConstructibleHeartBound` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.IntegralProperDirectSums` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.IntegralProperProjectionFormula` | unclaimed | definitionally the same canonical map; source unchanged |
| `Sheaf.Paper.IntegralQuotientDirectImageComparison` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.IntegralQuotientExchangeComparison` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.IntegralQuotientProjectionComparison` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.IntegralQuotientProjectionMap` | unclaimed | definitionally the same canonical map; source unchanged |
| `Sheaf.Paper.InterchangeProperPasting` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.LocalizingExceptionalAdjoint` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.LocalizingLowerShriekComposition` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.LocalizingLowerShriekCompositionModel` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.MateOpenRestriction` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.ModuleObjectProjectionMap` | unclaimed | definitionally the same canonical map; source unchanged |
| `Sheaf.Paper.NonrationalCompositionSeed` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.NonrationalLocalizingLowerShriekComposition` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.OpenImmersionLocalizing` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.ProEtaleProjectionExchangeMaps` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.ProEtaleProperOpenInterchange` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.ProjectionFiniteReduction` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.ProperBaseChangeRational` | unclaimed | definitionally the same canonical map; source unchanged |
| `Sheaf.Paper.ProperExceptionalRestriction` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.ProperHeartBound` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.ProperHeartConstructibleCohomology` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.ProperIndConstructibleBoundedBelow` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.ProperIndConstructibleUnbounded` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.ProperLocalizingAdmissibleCoefficients` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.ProperLocalizingContinuousAlgCl` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.ProperOpenBoundaryZero` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.ProperUnboundedCoproductComparison` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.ProperUnboundedCoproducts` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.ProperUnboundedWindow` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.ProperUnboundedWindowIso` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.QbarPerverseSubcategories` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.QbarPerverseSupportCondition` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.RationalExceptionalRestriction` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.RationalHomScalarTranspose` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.RationalLocalizingProjectionFormula` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.RationalRestrictionGlue` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.RationalScalarTransposeCompatibility` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.RationalTensorSymmetry` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.RationalVerdierEvaluationAdjoints` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.RestrictionLocal` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.ScalarExchangeConstituents` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.SfBidualityClass` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.SitePerfectRationalBidual` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.SmoothPullbackSupportDimension` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.TateTwistSupportCondition` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.TensorAdjunctionExchange` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.TowerCompactSupportProjectionFormula` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.TraceBaseChangeSecond` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.TraceFormulaDualizingComplex` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.TraceFormulaTopologicalInvariance` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.UnboundedBaseChangeExtension` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.VaryingRingGraphSummand` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Paper.VerdierExchange` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.PoincareDuality.ModuleObjectProjectionMorphism` | C2 (new) | new proved normalization API |
| `Sheaf.PoincareDuality.ProperProjectionFormulaBounded` | C2 | completed proof uses normalization API |
| `Sheaf.SecSmoothPurity.FiniteGeneralRing` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.SecSmoothPurity.MixedBaseChange` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.SecSmoothPurity.PurityDncCoefficientTransport` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.SecSmoothPurity.ReductionCompatibilities` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.SecSmoothPurity.ReductionDirectImage` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.SecSmoothPurity.ReductionExceptional` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.SecSmoothPurity.RestrictionTransitionTranspose` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.SixFunctors.CoefDualFormulaScalarTranspose` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtension` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.SixFunctors.CoefQbarVerdier` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.SixFunctors.CoefTowerEvaluationPairing` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.SixFunctors.CoefTowerNaturalCurrying` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.SixFunctors.CoefTowerTraceRectification` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.SixFunctors.CoefVerdierWeilEquivariance` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.SixFunctors.CtfStabilityDirectImages` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.SixFunctors.DetSfCompCompositionBaseChange` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.SixFunctors.FiniteAdjunctionSystemData` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.SixFunctors.FiniteAdjunctionTransition` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.SixFunctors.FiniteCoefficientVerdier` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.SixFunctors.FiniteDualizing` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.SixFunctors.FiniteExceptional` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.SixFunctors.FiniteMappingAdjunction` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.SixFunctors.IntegralBrownAdjoint` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.SixFunctors.IntegralComplementFiniteness` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.SixFunctors.IntegralDualizing` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.SixFunctors.IntegralExceptionalAffineChart` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.SixFunctors.IntegralExceptionalAffineFactorization` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.SixFunctors.IntegralExceptionalRestriction` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.SixFunctors.IntegralLocalizingCompactSupport` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.SixFunctors.IntegralRestrictionBoundedDescent` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.SixFunctors.IntegralRestrictionChartCover` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.SixFunctors.IntegralRestrictionClosed` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.SixFunctors.IntegralRestrictionGlue` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.SixFunctors.IntegralRestrictionLine` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.SixFunctors.IntegralVerdier` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.SixFunctors.NormalizedTowerTensorEvaluation` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.SixFunctors.ProperImageLocalizingProper` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.SixFunctors.RationalOperations` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.SixFunctors.RationalRetractEvaluation` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.SixFunctors.RationalVerdier` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.SmoothPurity.NormalizedWitness` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Targets.AffineSpaceRationalLine` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Targets.PoincareUncurry` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `Sheaf.Targets.SmoothPurityQbar` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `TargetsCheck` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `WeilConjectures` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `WeilConjectures.PoincareDuality.Poincare` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `WeilConjectures.PoincareDuality.ProjectionFormula` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `WeilConjectures.PoincareDuality.Verdier` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `WeilConjectures.SmoothPurity.Defs` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `WeilConjectures.TraceFormula.Basic` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `WeilConjectures.TraceFormula.Slop.Basic` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `WeilConjectures.TraceFormula.Slop.CompactCohomology` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `WeilConjectures.TraceFormula.Slop.Correspondence` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `WeilConjectures.TraceFormula.Slop.Dualizing` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `WeilConjectures.TraceFormula.Slop.FixedPoint` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `WeilConjectures.TraceFormula.Slop.Frobenius` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `WeilConjectures.TraceFormula.Slop.Main` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `WeilConjectures.TraceFormula.Slop.Stalk` | unclaimed | transitive importer; same definitions and statements; source unchanged |
| `WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek` | unclaimed | transitive importer; same definitions and statements; source unchanged |

## Status

landed 20261022T040148-L-2814682 2026-10-22 (merge of deliver/C2/Sheaf.PoincareDuality.ProperProjectionFormulaBounded)
