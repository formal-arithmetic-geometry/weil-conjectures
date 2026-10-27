# AlgebraicGeometry.ProEtale.CondensedRing.integralProperProjection

## Reason

Lean omitted the surrounding field and finite-type separated scheme hypotheses from
integralProperProjection: none occurs in its displayed conclusion. Its intended theorem,
the blueprint unit sk-thm-sf-pf-adic, is explicitly in the standing positive-characteristic
field setting. Retain that setting with `include k in` so the existing detail projection
and base-change theorems apply. No target statement or definition changes. The mathematical
DAG statement already has this setting and needs no correction. The item has no external
Lean caller of integralProperProjection. Its existing open-image caller already supplies
all standing hypotheses.

The open-image proof also uses the existing proved embedded/spectral coefficient isomorphism
and exact scalar restriction; no coefficient object is redefined. All added imports are proof
imports. Every public import stays unchanged, and every new helper is private and proved.

## Old

The following declaration occurs after the original section variables. Lean's printed
context drops k, its field/characteristic instances, the scheme structure maps and their
finite-type/separated hypotheses, and f.IsOver.

```lean
theorem integralProperProjection
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X)))
    (L : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) Y)))
    (hK : localizingClosureProEtale (Profinite.padicIntegersRingObj ℓ E.val) X K)
    (hL : localizingClosureProEtale (Profinite.padicIntegersRingObj ℓ E.val) Y L) :
    localizingClosureProEtale (Profinite.padicIntegersRingObj ℓ E.val) Y
        (((derivedTensor (Profinite.padicIntegersRingObj ℓ E.val) Y).obj
          ((moduleObjectDerivedPushforward
            (Profinite.padicIntegersRingObj ℓ E.val) f).obj K)).obj L) ∧
      localizingClosureProEtale (Profinite.padicIntegersRingObj ℓ E.val) Y
        ((moduleObjectDerivedPushforward (Profinite.padicIntegersRingObj ℓ E.val) f).obj
          (((derivedTensor (Profinite.padicIntegersRingObj ℓ E.val) X).obj K).obj
            ((moduleObjectDerivedPullback (Profinite.padicIntegersRingObj ℓ E.val) f).obj L))) ∧
      IsIso (moduleObjectProjectionMap (Profinite.padicIntegersRingObj ℓ E.val) f K L)
```

## New

The exact same textual declaration is preceded by:

```lean
include k in
```

This retains k and the section instances depending on it. Its signature text remains:

```lean
theorem integralProperProjection
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X)))
    (L : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) Y)))
    (hK : localizingClosureProEtale (Profinite.padicIntegersRingObj ℓ E.val) X K)
    (hL : localizingClosureProEtale (Profinite.padicIntegersRingObj ℓ E.val) Y L) :
    localizingClosureProEtale (Profinite.padicIntegersRingObj ℓ E.val) Y
        (((derivedTensor (Profinite.padicIntegersRingObj ℓ E.val) Y).obj
          ((moduleObjectDerivedPushforward
            (Profinite.padicIntegersRingObj ℓ E.val) f).obj K)).obj L) ∧
      localizingClosureProEtale (Profinite.padicIntegersRingObj ℓ E.val) Y
        ((moduleObjectDerivedPushforward (Profinite.padicIntegersRingObj ℓ E.val) f).obj
          (((derivedTensor (Profinite.padicIntegersRingObj ℓ E.val) X).obj K).obj
            ((moduleObjectDerivedPullback (Profinite.padicIntegersRingObj ℓ E.val) f).obj L))) ∧
      IsIso (moduleObjectProjectionMap (Profinite.padicIntegersRingObj ℓ E.val) f K L)
```

The integralOpenDirectImage signature remains unchanged; its j.IsOver binder
already mentions k.

## Users

Complete transitive import audit from tools/downstream.py. Searching the sources including
quarantine found no caller of integralProperProjection outside this module. Only
Sheaf.SixFunctors.IntegralComplementFiniteness calls integralOpenDirectImage, with the
standing field and scheme data already supplied. No other module is edited.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.IntegralOpenImageProperFormulas | H4 | Restore the standing hypotheses and prove the corrected theorem. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.Paper.AdicCommonStageHomTranspose | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.Paper.AdicProperLocalizingAdjunctionComparison | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.Paper.CartesianSectionAdjointMates | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.Paper.CartesianSectionData | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.Paper.ChartDiagonalSourceMate | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.Paper.CondensedHomChainRealization | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.Paper.ExceptionalInverseImageExistence | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.Paper.GeometricComparisonData | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.Paper.GeometricOperations | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.Paper.NativeCompactProjectionFormula | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.Paper.PodHomChainCtfDomains | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.Paper.ProperExceptionalRestriction | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.Paper.ProperProductCounitTranspose | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.Paper.RationalHomScalarTranspose | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.Paper.RationalTensorSymmetry | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.Paper.RelativeProductInputDomains | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.Paper.SfBidualityClass | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.Paper.SfPackageCoefficientDomains | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.Paper.SfPackageLocalizationProjectionRealization | S4 | No reference to integralProperProjection; no adaptation. |
| Sheaf.Paper.SitePerfectRationalBidual | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.Paper.SystemProjectionFormulaCoherence | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.Paper.WeilChosenDualityExchange | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | V1 | No reference to integralProperProjection; no adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | V3 | No reference to integralProperProjection; no adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.SixFunctors.FiniteExceptional | X3 | No reference to integralProperProjection; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.SixFunctors.IntegralDualExceptionalSystem | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalMappingSystem | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionLine | G2 | No reference to integralProperProjection; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | Y3 | No reference to integralProperProjection; no adaptation. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | H7 | No reference to integralProperProjection; no adaptation. |
| Sheaf.SixFunctors.ScalarSixCtf | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.SixFunctors.ScalarSixDirectImage | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.SixFunctors.WeilChosenDualityHom | D2 | No reference to integralProperProjection; no adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | No reference to integralProperProjection; no adaptation. |
| Sheaf.WeilSheaf.NativePullbackStarPreservation | R3 | No reference to integralProperProjection; no adaptation. |
| TargetsCheck | unclaimed | No reference to integralProperProjection; no adaptation. |
| WeilConjectures | unclaimed | No reference to integralProperProjection; no adaptation. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | No reference to integralProperProjection; no adaptation. |
| WeilConjectures.PoincareDuality.Verdier | S6 | No reference to integralProperProjection; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ClopenLowerShriek | unclaimed | No reference to integralProperProjection; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.Coherence | unclaimed | No reference to integralProperProjection; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek | unclaimed | No reference to integralProperProjection; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | No reference to integralProperProjection; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | No reference to integralProperProjection; no adaptation. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | No reference to integralProperProjection; no adaptation. |
| WeilConjectures.TraceFormula.Additivity | unclaimed | No reference to integralProperProjection; no adaptation. |
| WeilConjectures.TraceFormula.BaseChangeCoherence | unclaimed | No reference to integralProperProjection; no adaptation. |
| WeilConjectures.TraceFormula.Basic | unclaimed | No reference to integralProperProjection; no adaptation. |
| WeilConjectures.TraceFormula.BorelMoore | unclaimed | No reference to integralProperProjection; no adaptation. |
| WeilConjectures.TraceFormula.CoefficientMorphism | unclaimed | No reference to integralProperProjection; no adaptation. |
| WeilConjectures.TraceFormula.CompactCohomology | unclaimed | No reference to integralProperProjection; no adaptation. |
| WeilConjectures.TraceFormula.CompactPullback | unclaimed | No reference to integralProperProjection; no adaptation. |
| WeilConjectures.TraceFormula.Correspondence | unclaimed | No reference to integralProperProjection; no adaptation. |
| WeilConjectures.TraceFormula.CorrespondencePair | unclaimed | No reference to integralProperProjection; no adaptation. |
| WeilConjectures.TraceFormula.CurvePieces | unclaimed | No reference to integralProperProjection; no adaptation. |
| WeilConjectures.TraceFormula.Dualizing | unclaimed | No reference to integralProperProjection; no adaptation. |
| WeilConjectures.TraceFormula.FibreCoherence | unclaimed | No reference to integralProperProjection; no adaptation. |
| WeilConjectures.TraceFormula.FibreModel | unclaimed | No reference to integralProperProjection; no adaptation. |
| WeilConjectures.TraceFormula.FixedPoint | unclaimed | No reference to integralProperProjection; no adaptation. |
| WeilConjectures.TraceFormula.FixedPointScheme | unclaimed | No reference to integralProperProjection; no adaptation. |
| WeilConjectures.TraceFormula.Frobenius | unclaimed | No reference to integralProperProjection; no adaptation. |
| WeilConjectures.TraceFormula.FrobeniusLocalTerm | unclaimed | No reference to integralProperProjection; no adaptation. |
| WeilConjectures.TraceFormula.KunnethVerdier | unclaimed | No reference to integralProperProjection; no adaptation. |
| WeilConjectures.TraceFormula.LefschetzVerdier | unclaimed | No reference to integralProperProjection; no adaptation. |
| WeilConjectures.TraceFormula.LocalTerm | unclaimed | No reference to integralProperProjection; no adaptation. |
| WeilConjectures.TraceFormula.LocalTermLocality | unclaimed | No reference to integralProperProjection; no adaptation. |
| WeilConjectures.TraceFormula.ModelExtension | unclaimed | No reference to integralProperProjection; no adaptation. |
| WeilConjectures.TraceFormula.OpenPieceCoherence | unclaimed | No reference to integralProperProjection; no adaptation. |
| WeilConjectures.TraceFormula.OpenSquare | unclaimed | No reference to integralProperProjection; no adaptation. |
| WeilConjectures.TraceFormula.PointNormalization | unclaimed | No reference to integralProperProjection; no adaptation. |
| WeilConjectures.TraceFormula.Product | unclaimed | No reference to integralProperProjection; no adaptation. |
| WeilConjectures.TraceFormula.ProperCompatibility | unclaimed | No reference to integralProperProjection; no adaptation. |
| WeilConjectures.TraceFormula.ProperCurve | unclaimed | No reference to integralProperProjection; no adaptation. |
| WeilConjectures.TraceFormula.ProperPushforward | unclaimed | No reference to integralProperProjection; no adaptation. |
| WeilConjectures.TraceFormula.ProperPushforwardKernel | unclaimed | No reference to integralProperProjection; no adaptation. |
| WeilConjectures.TraceFormula.RelativeFrobenius | unclaimed | No reference to integralProperProjection; no adaptation. |
| WeilConjectures.TraceFormula.RelativeFrobeniusComparison | unclaimed | No reference to integralProperProjection; no adaptation. |
| WeilConjectures.TraceFormula.RelativeFrobeniusIterate | unclaimed | No reference to integralProperProjection; no adaptation. |
| WeilConjectures.TraceFormula.Stalk | unclaimed | No reference to integralProperProjection; no adaptation. |
| WeilConjectures.TraceFormula.SupportedPairing | unclaimed | No reference to integralProperProjection; no adaptation. |
| WeilConjectures.TraceFormula.TraceClass | unclaimed | No reference to integralProperProjection; no adaptation. |
| WeilConjectures.TraceFormula.TraceClassAdditivity | unclaimed | No reference to integralProperProjection; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | No reference to integralProperProjection; no adaptation. |

## Status

landed 20261024T223329-L-1585087 2026-10-24 (merge of deliver/H4/Sheaf.Paper.IntegralOpenImageProperFormulas)
