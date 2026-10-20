# AlgebraicGeometry.Etale.properCoefficientComplexMap

## Reason

The composite of complex-functor composition isomorphisms obscures the degreewise ordinary coefficient map when the kernel checks the model square. Construct the chain map directly: its nth component is properSheafCoefficientMap at C.X n, and its differential compatibility is the ordinary naturality equation. The former composition isomorphisms have identity components, so this is precisely the same termwise map, with the same source, target, and public signature. No data is chosen from an unproved theorem.

## Old

```lean
def properCoefficientComplexMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {W V : Scheme.{u}} (r : W ⟶ V)
    (C : CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    coefficientExtendedComplex φ V
        (((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).obj C) ⟶
      ((lowerStar (ModuleCat.{u + 1} B) r).mapHomologicalComplex (.up ℤ)).obj
        (coefficientExtendedComplex φ W C) :=
  (Functor.mapHomologicalComplexCompIso
      (Iso.refl (lowerStar (ModuleCat.{u + 1} A) r ⋙
        ProEtale.etaleSheafExtendScalars φ V)) (.up ℤ)).hom.app C ≫
    (NatTrans.mapHomologicalComplex (properSheafCoefficientMap φ r) (.up ℤ)).app C ≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (ProEtale.etaleSheafExtendScalars φ W ⋙
        lowerStar (ModuleCat.{u + 1} B) r)) (.up ℤ)).inv.app C
```

## New

```lean
def properCoefficientComplexMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {W V : Scheme.{u}} (r : W ⟶ V)
    (C : CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    coefficientExtendedComplex φ V
        (((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).obj C) ⟶
      ((lowerStar (ModuleCat.{u + 1} B) r).mapHomologicalComplex (.up ℤ)).obj
        (coefficientExtendedComplex φ W C) :=
  { f n := (properSheafCoefficientMap φ r).app (C.X n)
    comm' i j _ := ((properSheafCoefficientMap φ r).naturality (C.d i j)).symm }
```

The item proof checks the ordinary mate counit identity degreewise and constructs a natural transformation whose components are this chain map.

## Users

The only direct declaration user is the item module itself. The table also lists every transitive importer reported by tools/downstream.py --uses. No consumer statement or map changes.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Degreewise map and public type preserved; no consumer edit. |
| Sheaf.Paper.AcyclicFlatProperCoefficientModel | U3 | Constructs the same chain map directly degreewise; proves its mate identity and naturality. |
| Sheaf.Paper.AdmissibleVerdierExchange | unclaimed | Degreewise map and public type preserved; no consumer edit. |
| Sheaf.Paper.CoefficientTowerGeometricComposition | unclaimed | Degreewise map and public type preserved; no consumer edit. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | Degreewise map and public type preserved; no consumer edit. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Degreewise map and public type preserved; no consumer edit. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | Degreewise map and public type preserved; no consumer edit. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Degreewise map and public type preserved; no consumer edit. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | unclaimed | Degreewise map and public type preserved; no consumer edit. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed | Degreewise map and public type preserved; no consumer edit. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | unclaimed | Degreewise map and public type preserved; no consumer edit. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed | Degreewise map and public type preserved; no consumer edit. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | T5 | Degreewise map and public type preserved; no consumer edit. |
| Sheaf.Paper.FiniteFreeCompactComposition | unclaimed | Degreewise map and public type preserved; no consumer edit. |
| Sheaf.Paper.FiniteFreeCompactScalar | unclaimed | Degreewise map and public type preserved; no consumer edit. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | unclaimed | Degreewise map and public type preserved; no consumer edit. |
| Sheaf.Paper.FiniteFreeProjectionExchange | unclaimed | Degreewise map and public type preserved; no consumer edit. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | unclaimed | Degreewise map and public type preserved; no consumer edit. |
| Sheaf.Paper.FiniteFreeScalarProjection | unclaimed | Degreewise map and public type preserved; no consumer edit. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Degreewise map and public type preserved; no consumer edit. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Degreewise map and public type preserved; no consumer edit. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | Degreewise map and public type preserved; no consumer edit. |
| Sheaf.Paper.GlobalVerdierDuality | unclaimed | Degreewise map and public type preserved; no consumer edit. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Degreewise map and public type preserved; no consumer edit. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Degreewise map and public type preserved; no consumer edit. |
| Sheaf.Paper.RationalHomScalarTranspose | unclaimed | Degreewise map and public type preserved; no consumer edit. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | unclaimed | Degreewise map and public type preserved; no consumer edit. |
| Sheaf.Paper.RationalTensorSymmetry | unclaimed | Degreewise map and public type preserved; no consumer edit. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | unclaimed | Degreewise map and public type preserved; no consumer edit. |
| Sheaf.Paper.ScalarExchangeConstituents | unclaimed | Degreewise map and public type preserved; no consumer edit. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Degreewise map and public type preserved; no consumer edit. |
| Sheaf.Paper.SitePerfectRationalBidual | unclaimed | Degreewise map and public type preserved; no consumer edit. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Degreewise map and public type preserved; no consumer edit. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Degreewise map and public type preserved; no consumer edit. |
| Sheaf.Paper.TensorAdjunctionExchange | unclaimed | Degreewise map and public type preserved; no consumer edit. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | Degreewise map and public type preserved; no consumer edit. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Degreewise map and public type preserved; no consumer edit. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | Degreewise map and public type preserved; no consumer edit. |
| Sheaf.Paper.VerdierExchange | unclaimed | Degreewise map and public type preserved; no consumer edit. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Degreewise map and public type preserved; no consumer edit. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | Degreewise map and public type preserved; no consumer edit. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | Degreewise map and public type preserved; no consumer edit. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | Degreewise map and public type preserved; no consumer edit. |
| Sheaf.SecSmoothPurity.ReductionExceptional | unclaimed | Degreewise map and public type preserved; no consumer edit. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Degreewise map and public type preserved; no consumer edit. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Degreewise map and public type preserved; no consumer edit. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | Degreewise map and public type preserved; no consumer edit. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed | Degreewise map and public type preserved; no consumer edit. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | unclaimed | Degreewise map and public type preserved; no consumer edit. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed | Degreewise map and public type preserved; no consumer edit. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | unclaimed | Degreewise map and public type preserved; no consumer edit. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | unclaimed | Degreewise map and public type preserved; no consumer edit. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | Degreewise map and public type preserved; no consumer edit. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | unclaimed | Degreewise map and public type preserved; no consumer edit. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | Degreewise map and public type preserved; no consumer edit. |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed | Degreewise map and public type preserved; no consumer edit. |
| Sheaf.SixFunctors.FiniteExceptional | unclaimed | Degreewise map and public type preserved; no consumer edit. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Degreewise map and public type preserved; no consumer edit. |
| Sheaf.SixFunctors.IntegralVerdier | V2 | Degreewise map and public type preserved; no consumer edit. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | unclaimed | Degreewise map and public type preserved; no consumer edit. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Degreewise map and public type preserved; no consumer edit. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed | Degreewise map and public type preserved; no consumer edit. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | Degreewise map and public type preserved; no consumer edit. |

## Status

landed 20261020T221353-L-4179136 2026-10-20 (merge of deliver/U3/Sheaf.Paper.AcyclicFlatProperCoefficientModel)
