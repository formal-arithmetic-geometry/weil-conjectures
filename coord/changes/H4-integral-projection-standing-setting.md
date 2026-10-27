# AlgebraicGeometry.ProEtale.CondensedRing.integralProperProjection

## Reason

The mathematical node and source assume the standing separated finite-type setting over
k of positive characteristic different from ell. The original theorem's conclusion does
not mention k, so Lean silently omitted k, its Field/Fact instances, the two Over structures,
the finite-type/quasi-compact/separated structure-map hypotheses and the IsOver f instance.
Compilation of the planned proof therefore failed with `Unknown identifier k`; its printed
goal context contained only ell, E, X, Y, f and IsProper f. The detail projection theorem
correctly requires the standing setting. Restore those already intended hypotheses by
`include k in` immediately before this theorem. No definition, target or source-library
signature changes.

## Old

The following declaration occurred after the section variables shown in the item source,
without an include command. Consequently the standing base-field assumptions were omitted
from its elaborated type.

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

The declaration text is identical, with this scoped command before its docstring:

```lean
include k in
```

Thus its elaborated type now includes `(k : Type u) [Field k]`, the two characteristic
Fact instances, X.Over and Y.Over, all six structure-map finiteness/separatedness hypotheses,
and `[f.IsOver (Spec (.of k))]`, in addition to the original parameters. The complete
corrected declaration and proof are in lean/Sheaf/Paper/IntegralOpenImageProperFormulas.lean.
The natural-language node statement and all of its clients' mathematical assertions stay
unchanged: this repairs only the Lean encoding of its documented standing setting.

## Users

`python3 tools/downstream.py Sheaf.Paper.IntegralOpenImageProperFormulas --uses
integralProperProjection` listed the following downstream modules. Its uses scan found
only the declaration in the item itself. A separate rg search over both library roots
confirmed zero theorem callers. None of these modules needs adaptation; no held module is
edited. Imports and the other two theorem types remain unchanged.

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
