# AlgebraicGeometry.Etale.properAcyclicComparison

## Reason

The comparison is bundled as a natural transformation in generic abelian
categories and then specialized directly to the concrete sheaf categories.
Its component is the same quotient-factor map followed by the same derived unit.
The repaired packet removes redundant reflexive equality transports and uses a
proved generic adjunction pasting calculation for the coefficient square. This
avoids repeatedly unfolding concrete sheaf functors during kernel checking.
There is no choice of new data or new hypothesis.

## Old

```lean
def properAcyclicComparison
    (A : Type (u + 1)) [CommRing A] {W V : Scheme.{u}} (r : W ⟶ V)
    (C : CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    DerivedCategory.Q.obj
        (((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).obj C) ⟶
      (rightDerivedLowerStar (ModuleCat.{u + 1} A) r).obj (DerivedCategory.Q.obj C) :=
  DerivedCategory.Qh.map
      (((lowerStar (ModuleCat.{u + 1} A) r).mapHomotopyCategoryFactors (.up ℤ)).inv.app C) ≫
    (lowerStar (ModuleCat.{u + 1} A) r).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj C)
```

## New

```lean
def properAcyclicComparison
    (A : Type (u + 1)) [CommRing A] {W V : Scheme.{u}} (r : W ⟶ V)
    (C : CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    DerivedCategory.Q.obj
        (((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).obj C) ⟶
      (rightDerivedLowerStar (ModuleCat.{u + 1} A) r).obj (DerivedCategory.Q.obj C) :=
  (properAcyclicComparisonTransformation A r).app C
```

The new public support declarations are acyclicComplexComparisonTransformation
and properAcyclicComparisonTransformation. Both are actual constructions.
Existing public signatures and imports remain unchanged.

## Users

The following table includes the module itself and every transitive importer listed by tools/downstream.py --uses. The canonical maps and all public types are preserved, so no consumer source adaptation is required. The definition representation and this assertion are submitted for independent review.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Canonical map and public type preserved; no consumer edit. |
| Sheaf.Paper.AcyclicFlatProperCoefficientModel | U3 | Uses the bundled comparison API in the item proof. |
| Sheaf.Paper.AdmissibleVerdierExchange | unclaimed | Canonical map and public type preserved; no consumer edit. |
| Sheaf.Paper.CoefficientTowerGeometricComposition | unclaimed | Canonical map and public type preserved; no consumer edit. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | Canonical map and public type preserved; no consumer edit. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Canonical map and public type preserved; no consumer edit. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | Canonical map and public type preserved; no consumer edit. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Canonical map and public type preserved; no consumer edit. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | unclaimed | Canonical map and public type preserved; no consumer edit. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed | Canonical map and public type preserved; no consumer edit. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | unclaimed | Canonical map and public type preserved; no consumer edit. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed | Canonical map and public type preserved; no consumer edit. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | T5 | Canonical map and public type preserved; no consumer edit. |
| Sheaf.Paper.FiniteFreeCompactComposition | unclaimed | Canonical map and public type preserved; no consumer edit. |
| Sheaf.Paper.FiniteFreeCompactScalar | unclaimed | Canonical map and public type preserved; no consumer edit. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | unclaimed | Canonical map and public type preserved; no consumer edit. |
| Sheaf.Paper.FiniteFreeProjectionExchange | unclaimed | Canonical map and public type preserved; no consumer edit. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | unclaimed | Canonical map and public type preserved; no consumer edit. |
| Sheaf.Paper.FiniteFreeScalarProjection | unclaimed | Canonical map and public type preserved; no consumer edit. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Canonical map and public type preserved; no consumer edit. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Canonical map and public type preserved; no consumer edit. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | Canonical map and public type preserved; no consumer edit. |
| Sheaf.Paper.GlobalVerdierDuality | unclaimed | Canonical map and public type preserved; no consumer edit. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Canonical map and public type preserved; no consumer edit. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Canonical map and public type preserved; no consumer edit. |
| Sheaf.Paper.RationalHomScalarTranspose | unclaimed | Canonical map and public type preserved; no consumer edit. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | unclaimed | Canonical map and public type preserved; no consumer edit. |
| Sheaf.Paper.RationalTensorSymmetry | unclaimed | Canonical map and public type preserved; no consumer edit. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | unclaimed | Canonical map and public type preserved; no consumer edit. |
| Sheaf.Paper.ScalarExchangeConstituents | unclaimed | Canonical map and public type preserved; no consumer edit. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Canonical map and public type preserved; no consumer edit. |
| Sheaf.Paper.SitePerfectRationalBidual | unclaimed | Canonical map and public type preserved; no consumer edit. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Canonical map and public type preserved; no consumer edit. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Canonical map and public type preserved; no consumer edit. |
| Sheaf.Paper.TensorAdjunctionExchange | unclaimed | Canonical map and public type preserved; no consumer edit. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | Canonical map and public type preserved; no consumer edit. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Canonical map and public type preserved; no consumer edit. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | Canonical map and public type preserved; no consumer edit. |
| Sheaf.Paper.VerdierExchange | unclaimed | Canonical map and public type preserved; no consumer edit. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Canonical map and public type preserved; no consumer edit. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | Canonical map and public type preserved; no consumer edit. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | Canonical map and public type preserved; no consumer edit. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | Canonical map and public type preserved; no consumer edit. |
| Sheaf.SecSmoothPurity.ReductionExceptional | unclaimed | Canonical map and public type preserved; no consumer edit. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Canonical map and public type preserved; no consumer edit. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Canonical map and public type preserved; no consumer edit. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | Canonical map and public type preserved; no consumer edit. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed | Canonical map and public type preserved; no consumer edit. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | unclaimed | Canonical map and public type preserved; no consumer edit. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed | Canonical map and public type preserved; no consumer edit. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | unclaimed | Canonical map and public type preserved; no consumer edit. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | unclaimed | Canonical map and public type preserved; no consumer edit. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | Canonical map and public type preserved; no consumer edit. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | unclaimed | Canonical map and public type preserved; no consumer edit. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | Canonical map and public type preserved; no consumer edit. |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed | Canonical map and public type preserved; no consumer edit. |
| Sheaf.SixFunctors.FiniteExceptional | unclaimed | Canonical map and public type preserved; no consumer edit. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Canonical map and public type preserved; no consumer edit. |
| Sheaf.SixFunctors.IntegralVerdier | V2 | Canonical map and public type preserved; no consumer edit. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | unclaimed | Canonical map and public type preserved; no consumer edit. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Canonical map and public type preserved; no consumer edit. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed | Canonical map and public type preserved; no consumer edit. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | Canonical map and public type preserved; no consumer edit. |

## Status

landed 20261020T221353-L-4179136 2026-10-20 (merge of deliver/U3/Sheaf.Paper.AcyclicFlatProperCoefficientModel)
