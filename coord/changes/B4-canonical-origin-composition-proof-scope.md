# CanonicalOriginCompactSupportComposition proof scope and imports

## Reason

The four original holes are proved using the specified etale compositor and actual
site-comparison maps. Eighteen private proof imports used only by the older plan are
removed. All original public imports are retained verbatim. The private import of
Sheaf.Paper.CompactificationCoherence is retained for the blueprint unit route,
even though the formal unit and associativity equations need only the existing
etale equations. No unit statement or route module is withdrawn.

Local irreducibility attributes keep the large chosen comparison isomorphisms and
functors folded during proof unification. They are scoped to this file and do not
change attributes seen by importers. Without this control the compiler can exceed
60 seconds by expanding the chosen comparison constructions; with it the complete
module compiled in 17.4 seconds. The original public definition bodies, declaration
signatures, visibility, instances, and global attributes are unchanged. No target
meaning changes and no statement review is reopened.

The static checker requests this record for the local attribute commands. There is
no forced consumer adaptation: the public import list and every existing public
signature and data body remain the same.

## Old

The original imports, verbatim:

```lean
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekComposition
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriek
public import WeilConjectures.SixFunctors.ProEtale.ExceptionalAdjoint
public import Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
public import Sheaf.Paper.EtaleOriginDerivedCategory
import Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons
import Sheaf.AlgebraicGeometry.CompactifiableOverField
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
import Sheaf.AlgebraicGeometry.CompactifiableCompatibleTower
import Sheaf.AlgebraicGeometry.ComparisonDirectImage
import Sheaf.AlgebraicGeometry.CompatibleCompactificationTriangle
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroAdjunction
import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact
import Sheaf.AlgebraicGeometry.ProperOpenComparisonSiteNormalization
import Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence
import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
import Sheaf.Paper.CompactificationCoherence
import Sheaf.Paper.ComparisonPullbackExact
import Sheaf.Paper.FiniteDirectImageComposition
import Sheaf.Paper.RefinementComparisonIsomorphism
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
```

There were no local irreducibility attribute commands for these declarations.

## New

The delivered imports:

```lean
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekComposition
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
public import Sheaf.Paper.EtaleOriginDerivedCategory
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriek
public import WeilConjectures.SixFunctors.ProEtale.ExceptionalAdjoint
public import WeilConjectures.Compactification.RefinementCategory
import Sheaf.Paper.CompactificationCoherence
```

The new local proof attributes (in their respective scopes):

```lean
attribute [local irreducible] originComparison originComposition

attribute [local irreducible] originCompactSupportId
  originCompactSupportCongr originCompactSupport comparisonUpperStarPlusEtaleOrigin
  Etale.rightDerivedLowerShriekPlusCompIso Etale.rightDerivedLowerShriekPlus
  CompactSupportFormalism.lowerShriekId CompactSupportFormalism.lowerShriekCongr
```

The statements and bodies of every existing public definition are unchanged;
the four existing theorem proofs replace their original `sorry` bodies.

## Users

A source import-graph scan was checked against tools/downstream.py and its --uses
output. The table includes every transitive importer (including preserved sources
listed for rework), not just the six active consumers reported by server preflight.
Their existing statements retain their exact meaning: public names, public imports,
notations, instance visibility, and original data constructions are identical.
The local proof attributes are not exported. Every consumer remains untouched;
no consumer compilation is needed to establish this textual interface preservation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CanonicalOriginCompactSupportComposition | B4 | Four proofs completed; local proof attributes only |
| Sheaf.AlgebraicGeometry.ProjectionComparisonEtaleOrigin | P4 | Unchanged; no adaptation; identical public interface |
| Sheaf.AlgebraicGeometry.ProperCompositionSiteTransport | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.AdicPurityFiniteTensor | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.AdicPurityObjects | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.AdicPurityRootComparisons | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.AdicPuritySourceReduction | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.AdicPurityTwistReduction | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.AdmissibleVerdierExchange | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.CoefficientTowerGeometricComposition | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.CoefficientTowerSectionCoordinates | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.CoefficientTowerShriekInterfaces | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.CoefficientTowerTransitionCompatibility | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.CohomologicalSmoothComposition | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.CohomologicalSmoothnessTheorem | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.CompactSupportProjectionFormula | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.CompactSupportSiteCoherence | U4 | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.CompletedTensorHomTranspose | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.CompositeIntegrationCounit | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.ConstantExtensionCompactComparison | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.ConstructibleProjectionMates | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.CoprojectionCompositionMate | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.EtaleRhoMonoidalMate | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.FiniteClosedShriek | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.FiniteEtaleDescent | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.FiniteForwardProductSymmetry | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.FiniteFreeCoefficientExtension | T5 | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.FiniteFreeCompactComposition | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.FiniteFreeCompactScalar | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.FiniteFreeProjectionExchange | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.FiniteFreeScalarProjection | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.FiniteProductCompactification | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.FiniteStructuralMapsCommShift | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.FiniteTorStability | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.GlobalVerdierDuality | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.HomFiniteProjective | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.LocalFrobeniusConjugacy | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.ProEtaleCompositionTowerNormalization | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.ProjectionFiniteReduction | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.PurityDiagonalDualizingObject | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.PurityDiagonalSectionPasting | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.PurityDncFamilyIntrinsic | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.PurityFiniteExceptionalComposition | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.PurityGeneralAdmissibility | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.RationalHomScalarTranspose | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.RationalScalarTransposeCompatibility | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.RationalSmoothPurityCanonical | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.RationalStalkExact | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.RationalTensorSymmetry | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.ScalarExchangeConstituents | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.SfBidualityClass | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.SitePerfectCoefficientDual | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.SitePerfectDualizableHom | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.SitePerfectRationalBidual | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.SixFunctorDatum | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.SixFunctorDualNotation | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.SixFunctorOperationDatum | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.SixFunctorOperationDatumStages | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.SmoothPurityMap | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.SmoothTrace | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.StandingExceptionalComposition | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.TensorAdjunctionExchange | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.TraceCohomologicalCorrespondence | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.TraceExceptionalAdmissibility | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.TraceFixedScheme | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.TraceGraphCorrespondence | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.TwistFrobeniusScalar | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.VerdierExchange | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.WeilConstantExtensionFrobenius | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.Paper.WeilPullbackLocalFrobenius | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.SixFunctors.CompactCoefficientComposition | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.SixFunctors.FiniteExceptional | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.SixFunctors.FrobeniusFixedPoints | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.SixFunctors.IntegralVerdier | V2 | Unchanged; no adaptation; identical public interface |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed | Unchanged; no adaptation; identical public interface |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | Unchanged; no adaptation; identical public interface |

## Status

landed 20261020T211635-L-3481812 2026-10-20 (merge of deliver/B4/Sheaf.Paper.CanonicalOriginCompactSupportComposition)
