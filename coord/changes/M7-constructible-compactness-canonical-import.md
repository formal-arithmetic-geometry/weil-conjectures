# Sheaf.Paper.ConstructibleCompactness public import cleanup

## Reason

The return at head 956005c8d rejected a duplicate packet: its canonical compact-object
import repair was already present in the library. The current live source also has
zero local holes. Preserve that repair, and remove the unused public import of
`Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`, as required by
stage-3 import pruning. No statement or proof in this module uses the arbitrary
K-injective-resolution right-derived-functor construction.

This is the sole Lean change relative to the current live source. All declaration
signatures, bodies, attributes and docstrings remain identical. The canonical
`public import WeilConjectures.CategoryTheory.CompactObject` stays. No target
statement or definition changes meaning, and no target statement review is reopened.
This packet makes no claim that the already-present canonical import is a new repair.

## Old

```lean
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Sheaf.Paper.LocalizingClosureExistence
```

## New

```lean
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.LocalizingClosureExistence
```

## Users

`tools/downstream.py` finds 126 transitive consumers. Only
`Sheaf.Paper.BrownHypothesesGeneration` directly imports the item and uses
`HasConstructibleCompactness`. The public-import closure loses precisely
`Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`,
`Sheaf.CategoryTheory.KInjectiveTotalDerived` and
`Mathlib.CategoryTheory.Triangulated.Functor`; none is needed by this module's
public statements. The ordinary import closure is unchanged, since other proof
imports still reach them. No whole module is withdrawn or pruned from the targets.

`tools/import_prune_check.py` passes: no downstream declaration use loses its
required import. The importing compactness probe and unchanged direct consumer
are checked against the changed root with lcompile.py. No consumer is edited.
The table below records all consumers and their current local claim holders.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | C5 | Transitive consumer; no adaptation. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.Paper.AdmissibleVerdierExchange | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.Paper.AffineSpaceRationalInduction | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.Paper.BrownExceptionalAdjoint | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.Paper.BrownHypothesesGeneration | unclaimed | Direct consumer; no adaptation. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.Paper.CoefficientTowerGeometricComposition | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.Paper.CoefficientTowerSectionCoordinates | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekInterfaces | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.Paper.CoefficientTowerTransitionCompatibility | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.Paper.ConstructibleCompactness | M7 | Remove unused public import; all declarations and proofs identical. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.Paper.ExceptionalInverseImageExistence | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactComposition | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactScalar | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchange | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.Paper.FiniteFreeScalarProjection | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.Paper.GlobalVerdierDuality | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekComposition | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.Paper.MateOpenRestriction | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.Paper.NonrationalCompositionSeed | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.Paper.ProjectionFiniteReduction | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.Paper.ProperExceptionalRestriction | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.Paper.RationalExceptionalRestriction | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.Paper.RationalHomScalarTranspose | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.Paper.RationalRestrictionGlue | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.Paper.RationalTensorSymmetry | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.Paper.RestrictionLocal | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.Paper.ScalarExchangeConstituents | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.Paper.SitePerfectRationalBidual | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.Paper.TensorAdjunctionExchange | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.Paper.VerdierExchange | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptional | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.SixFunctors.FiniteExceptional | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.Targets.PoincareUncurry | unclaimed | Transitive consumer; no adaptation. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Transitive consumer; no adaptation. |
| TargetsCheck | unclaimed | Transitive consumer; no adaptation. |
| WeilConjectures | unclaimed | Transitive consumer; no adaptation. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Transitive consumer; no adaptation. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | Transitive consumer; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Transitive consumer; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Transitive consumer; no adaptation. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | Transitive consumer; no adaptation. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Transitive consumer; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | Transitive consumer; no adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Transitive consumer; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Transitive consumer; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Transitive consumer; no adaptation. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | Transitive consumer; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | Transitive consumer; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Transitive consumer; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | Transitive consumer; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Transitive consumer; no adaptation. |

## Status

landed 20261021T214843-L-1870169 2026-10-21 (merge of deliver/M7/Sheaf.Paper.ConstructibleCompactness)
