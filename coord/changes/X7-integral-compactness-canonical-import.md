# AlgebraicGeometry.ProEtale.IntegralConstructibleCompactnessAssertions

## Reason

Restore the module assigned by coord/rework.tsv from its quarantine archive and fix its
public compact-object import. The archived file fails at line 452: the public definition
cannot resolve `CategoryTheory.IsCompactObject`, because the old Sheaf module has been
withdrawn and the canonical upstream declaration is available only through private proof
imports. The compiler explicitly requests the upstream public import. This repair changes
one import line; every declaration, signature, definition body and theorem proof remains
verbatim. The theorem and definition have zero local holes before and after the repair.
No target statement or mathematical definition changes.

## Old

```lean
public import Sheaf.CategoryTheory.CompactObject
```

## New

```lean
public import WeilConjectures.CategoryTheory.CompactObject
```

## Users

`tools/downstream.py` reports the item as unknown because it is quarantined. A source import
graph over lean/Sheaf, lean/WeilConjectures and both corresponding quarantine roots finds
only the two direct archived consumers below and their transitive users. Live sources take
precedence over archives. No consumer is edited. All archived declarations and proof bodies
are preserved, and the replacement import exposes precisely the canonical compactness
notion used by the assertion. Individual direct-consumer compile results are in report.md.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | C5 | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.AdmissibleVerdierExchange | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.AffineSpaceRationalInduction | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.BrownExceptionalAdjoint | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.BrownHypothesesGeneration | unclaimed | Direct archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.CoefficientTowerGeometricComposition | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.CoefficientTowerSectionCoordinates | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekInterfaces | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.CoefficientTowerTransitionCompatibility | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.CompactificationCoherenceCocycle | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.CompactificationLocalizing | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.CompactificationRefinementIdentity | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.CompactificationRefinementLocalizing | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.ContinuousAlgClProperFiniteness | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.ContinuousAlgClProperHeartFiniteness | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.ContinuousAlgClProperLowerTail | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.ExceptionalInverseImageExistence | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactComposition | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactScalar | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchange | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.FiniteFreeScalarProjection | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.FrobeniusExchangeEquivalence | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.GeneralCondensedWeilRealization | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.GlobalVerdierDuality | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | M2 | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.IntegralProperDirectSums | unclaimed | Direct archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.IntegralProperProjectionFormula | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.InterchangeProperPasting | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekComposition | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekCompositionModel | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.MateOpenRestriction | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.NonrationalCompositionSeed | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.ProjectionFiniteReduction | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.ProperExceptionalRestriction | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.ProperLocalizingAdmissibleCoefficients | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.ProperLocalizingContinuousAlgCl | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.ProperProductCounitTranspose | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.RationalExceptionalRestriction | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.RationalHomScalarTranspose | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.RationalRestrictionGlue | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.RationalTensorSymmetry | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.RestrictionLocal | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.ScalarExchangeConstituents | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.SitePerfectRationalBidual | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.TensorAdjunctionExchange | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.TraceBaseChangeSecond | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.UnboundedBaseChangeExtension | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Paper.VerdierExchange | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptional | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.SixFunctors.FiniteExceptional | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Targets.PoincareUncurry | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| WeilConjectures.TraceFormula.Statement | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| WeilConjectures.TraceFormula.WeilTrace | unclaimed | Transitive archived consumer; same declarations; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Transitive archived consumer; same declarations; no adaptation. |

## Status

landed 20261021T170812-L-2762439 2026-10-21 (merge of deliver/X7/Sheaf.Paper.IntegralConstructibleCompactness)
