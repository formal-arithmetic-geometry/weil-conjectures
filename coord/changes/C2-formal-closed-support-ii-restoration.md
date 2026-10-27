# Sheaf.Paper.FormalClosedSupportII restoration

## Reason

Restore the complete zero-hole module from the quarantine path in coord/rework.tsv.
The upstream sync moved the private comparison Mod.relativeTensorRightIso into
Sheaf.UpstreamExtra.WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian.
The archived proof still imports all private declarations from its former upstream module.
Point that private import at the comparison's actual module. The existing public import
of the extra module is retained, along with every other public import.

Use a local irreducibility attribute for Mod.monoidalClosed to avoid expanding its
implementation during the private tensor proofs. It does not change the definition,
its exported attributes, or the selected monoidal closed structure.

All three public declarations and all docstrings remain identical to the archive.
Private proofs additionally qualify the monoidal tensor functors, enable backward
defeq lemmas, and use F.rightDerivedFunctorObjQIso I in place of its expanded
comparison through the homotopy category. The latter isomorphism is exactly the same
K-injective computation, packaged by the library; it has a private KInjective import. No target statement, definition body, or mathematical dependency changes.

## Old

The live source is quarantined. Relative to the preserved archive:

```lean
import all WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
```

No local irreducibility attribute follows the namespace openings.

## New

```lean
import all Sheaf.UpstreamExtra.WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
```

The proof imports additionally include:

```lean
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
```

The local elaboration option is:

```lean
set_option backward.defeqAttrib.useBackward true
```

After the namespace openings:

```lean
attribute [local irreducible] Mod.monoidalClosed
```

## Users

The stock downstream query reports unknown module because this item is quarantined.
The following inventory scans both live and quarantined Lean sources, with live sources
taking precedence. Every consumer retains the archived public interface and public
import closure; no consumer needs adaptation. The three direct importers are
Sheaf.Paper.UniformConstructibleExtIntegral,
Sheaf.Paper.UniformConstructibleExtTorsion, and
Sheaf.Paper.SupportedLatticeHomReductionTower. None explicitly names the three
public declarations; their use is through the retained imports and instances.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.AdmissibleVerdierExchange | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.AffineSpaceRationalInduction | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.BrownExceptionalAdjoint | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.BrownHypothesesGeneration | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | E2 | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.CoefficientTowerGeometricComposition | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.CoefficientTowerSectionCoordinates | E1 | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekInterfaces | A4 | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.CoefficientTowerTransitionCompatibility | E2 | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.ConstructibleCompactness | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.EtaleCtfChartDomain | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.EtaleSumCounitScalar | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.ExceptionalInverseImageExistence | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.FiniteCompactSupportDomains | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactComposition | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactScalar | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchange | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.FiniteFreeScalarProjection | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.FiniteWindow | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.FiniteWindowBounded | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.FiniteWindowUnbounded | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.FormalClosedSupportII | C2 | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.FrobeniusExchangeEquivalence | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.GeneralCondensedWeilRealization | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.GlobalVerdierDuality | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekComposition | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.MateOpenRestriction | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.NonrationalCompositionSeed | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.P1CounitScalar | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.P1SplittingScalar | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.ProjectionFiniteReduction | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.ProperExceptionalRestriction | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.ProperProductCounitTranspose | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.RationalExceptionalRestriction | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.RationalHomScalarTranspose | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.RationalRestrictionGlue | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.RationalTensorSymmetry | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.RestrictionLocal | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.ScalarExchangeConstituents | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.SitePerfectRationalBidual | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.SupportedLatticeHomReductionTower | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.TensorAdjunctionExchange | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.UniformConstructibleExt | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtIntegral | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtRational | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtTorsion | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Paper.VerdierExchange | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.SecSmoothPurity.ChartFiniteRingAdjunction | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptional | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.SixFunctors.FiniteExceptional | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypothesesFiniteFieldCompactness | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Targets.PoincareUncurry | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Archived public interface preserved; no adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Archived public interface preserved; no adaptation. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Archived public interface preserved; no adaptation. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | Archived public interface preserved; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Archived public interface preserved; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Archived public interface preserved; no adaptation. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | Archived public interface preserved; no adaptation. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Archived public interface preserved; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | Archived public interface preserved; no adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Archived public interface preserved; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Archived public interface preserved; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Archived public interface preserved; no adaptation. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | Archived public interface preserved; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | Archived public interface preserved; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Archived public interface preserved; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | Archived public interface preserved; no adaptation. |
| WeilConjectures.TraceFormula.Statement | unclaimed | Archived public interface preserved; no adaptation. |
| WeilConjectures.TraceFormula.WeilTrace | unclaimed | Archived public interface preserved; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Archived public interface preserved; no adaptation. |

## Status

landed 20261022T113834-L-291868 2026-10-22 (merge of deliver/C2/Sheaf.Paper.FormalClosedSupportII)
