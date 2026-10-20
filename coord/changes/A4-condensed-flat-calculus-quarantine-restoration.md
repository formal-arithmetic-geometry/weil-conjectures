# condensedFiniteCoefficientCalculus: quarantine restoration

## Reason

The assigned rework row preserves this zero-hole module in quarantine. Its public
Compatibility-extra import has no published object file, and its two finite-basis
helpers no longer exist in the synchronized adopted source. Restore the item and
its constructive private proof support. No adopted source file is changed.

## Old

```lean
public import Sheaf.Paper.CondensedCoefficientComparisons
import all Sheaf.Paper.CondensedFiniteModelProofAPI
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
```

The original private `point_finiteFree` and `scheme_finiteFree` proof bodies call
`Profinite.continuousBasisSheafIso` and `Mod.mapFreeRestrictedRegularIso` from the
old source file, using `import all`.

## New

```lean
public import Sheaf.Paper.CondensedCoefficientComparisons
import all Sheaf.Paper.CondensedFiniteModelProofAPI
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
```

`FiniteBasisConstruction` restores the private Map and RingIso helpers and the
continuous-function coordinate constructions from the archived Compatibility extra.
The constructions retain their original explicit terms and proofs; the only local
syntactic adaptation replaces the deprecated proof-level `letI` by `let`.
No source-library declaration is added, changed or removed. The former source
`import all` becomes unnecessary because the two callers resolve the local private
constructions. The unrelated bounded-pushforward extra is not needed for any item
statement or proof. All four public theorem signatures are verbatim from quarantine.

The new private section has its own universe declarations, opens and transparency
option; the section ends before the existing generic coherence proof scopes. Six
existing cache lemmas now omit the unused `MonoidalPreadditive C` section variable.
These are private proof elaboration changes only. No coefficient data or target
meaning changes; no forced adaptations are delivered.

## Users

The live `tools/downstream.py --allow-missing --names` query has no importers while
the item is quarantined. A second import-closure scan overlays live sources on the
quarantine archive, preserving every archived parent. The three direct users are
`CoefficientFiniteDescentHom`, `GeneralCondensedWeilRealization`, and
`CompactSupportCondensedRealization` under `Sheaf.Paper`; all import the item only
for proofs. The Hom-descent proof uses the unchanged second coherence clause.
The following complete archived closure is recorded conservatively; none is adapted.
The restored module is additionally checked through a fresh importer applying all
four declarations at their verbatim archived types.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | C5 | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.AdmissibleVerdierExchange | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.AffineSpaceRationalInduction | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.BrownExceptionalAdjoint | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.BrownHypothesesGeneration | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.CoefficientFiniteDescentHom | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.CoefficientTowerGeometricComposition | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.CoefficientTowerSectionCoordinates | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekInterfaces | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.CoefficientTowerTransitionCompatibility | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.CompactSupportCondensedRealization | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.CompactificationCoherenceCocycle | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.CompactificationLocalizing | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.CompactificationRefinementIdentity | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.CompactificationRefinementLocalizing | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.CondensedFlatCoefficientCalculus | A4 | Restored item; identical public theorem signatures. |
| Sheaf.Paper.ConstructibleCompactness | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.ContinuousAlgClProperFiniteness | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.ContinuousAlgClProperHeartFiniteness | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.ContinuousAlgClProperLowerTail | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.DerivedTruncationCoproducts | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.ExceptionalInverseImageExistence | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.FiniteCoefficientDescentTwoColimit | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | T5 | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactComposition | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactScalar | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchange | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.FiniteFreeScalarProjection | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.FiniteWindow | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.FiniteWindowBounded | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.FiniteWindowUnbounded | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.FrobeniusExchangeEquivalence | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.GeneralCondensedWeilRealization | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.GlobalVerdierDuality | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | M2 | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.IntegralProperCohomologicalBounds | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.IntegralProperDirectSums | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.IntegralProperProjectionFormula | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.InterchangeProperPasting | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekComposition | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekCompositionModel | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.MateOpenRestriction | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.NonrationalCompositionSeed | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.ProjectionFiniteReduction | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.ProperExceptionalRestriction | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.ProperHeartBound | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.ProperHeartBoundReduction | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.ProperHeartConstructibleCohomology | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.ProperIndConstructibleUnbounded | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.ProperLocalizingAdmissibleCoefficients | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.ProperLocalizingContinuousAlgCl | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.ProperProductCounitTranspose | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.ProperUnboundedCoproductComparison | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.ProperUnboundedCoproducts | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindow | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindowIso | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.RationalClosedSupportConstructible | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.RationalExceptionalRestriction | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.RationalHomScalarTranspose | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.RationalOpenDirectImageConstructible | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.RationalRestrictionGlue | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.RationalTensorSymmetry | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.RestrictionLocal | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.ScalarExchangeConstituents | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.SitePerfectRationalBidual | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.TensorAdjunctionExchange | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.TraceBaseChangeSecond | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.UnboundedBaseChangeExtension | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.UniformConstructibleExt | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtRational | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Paper.VerdierExchange | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptional | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.SixFunctors.FieldTensor | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.SixFunctors.FiniteExceptional | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | V2 | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Targets.PoincareUncurry | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| WeilConjectures.TraceFormula.Statement | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Quarantined consumer; identical theorem API; no adaptation. |

## Status

landed 20261020T154611-L-3135597 2026-10-20 (merge of deliver/A4/Sheaf.Paper.CondensedFlatCoefficientCalculus)
