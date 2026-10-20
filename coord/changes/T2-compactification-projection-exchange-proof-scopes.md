# AlgebraicGeometry.ProEtale.compactification_projection_exchange_coherence

## Reason

Complete the assigned canonical compactification projection/exchange identity using the
actual fixed-coefficient pro-etale operations. Add only fully proved private helpers and
private canonical comparison maps. Local priorities select existing proved instances, and
local transparency settings keep derived-functor constructions folded during elaboration.
The finite specialization selects the same Grothendieck-category colimit instances as the
generic argument. No construction or exported instance or reducibility attribute is changed.

Remove the five unused public imports and six obsolete proof imports. The public theorem
signature is unchanged. The retained public imports supply every name in that signature.
The only direct importer is Sheaf.Paper.CohomologicalSmoothComposition; no downstream source
mentions the theorem yet. The consumers and claim holders below were checked from sources. The unchanged direct
consumer compiled against the sandbox output in 9.5 seconds after rebuilding the item; no adaptation was needed.
The added scoped instance removals apply to one declaration at a time. Other local settings
and attributes affect this file only. They export no instance or attribute change.
No target, mathematical definition, source-library declaration, or consumer is changed.

## Old

```lean
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.SixFunctors.IntrinsicDerivedTensor
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero

theorem compactification_projection_exchange_coherence
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {T' T U' U : Scheme.{u}} {w : T' ⟶ T} {u' : T' ⟶ U'}
    {u : T ⟶ U} {v : U' ⟶ U}
    [IsSeparated u] [LocallyOfFiniteType u] [QuasiCompact u]
    (sq : IsPullback w u' u v) (c : Compactification u) [QuasiCompact c.i]
    (N : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} Λ)))
    (P : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} Λ))) :
    L((v)^*[ModuleCat.{u + 1} Λ]).map
        (((projectionMapOfCompactification (ModuleCat.{u + 1} Λ) c).app N).app P) ≫
      (rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat.{u + 1} Λ) sq c).app
        (((-⊗ᴸ-(T)[ModuleCat.{u + 1} Λ]).obj N).obj
          (L((u)^*[ModuleCat.{u + 1} Λ]).obj P)) ≫
      (Rf_!(c.ofIsPullback sq)[ModuleCat.{u + 1} Λ]).map
        (((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} Λ) w).app N).app
          (L((u)^*[ModuleCat.{u + 1} Λ]).obj P)) ≫
      (Rf_!(c.ofIsPullback sq)[ModuleCat.{u + 1} Λ]).map
        (((-⊗ᴸ-(T')[ModuleCat.{u + 1} Λ]).obj
          (L((w)^*[ModuleCat.{u + 1} Λ]).obj N)).map
            ((leftDerivedUpperStarSquareIso (ModuleCat.{u + 1} Λ) sq.toCommSq).inv.app P)) =
    ((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} Λ) v).app
        ((Rf_!(c)[ModuleCat.{u + 1} Λ]).obj N)).app P ≫
      ((-⊗ᴸ-(U')[ModuleCat.{u + 1} Λ]).map
        ((rightDerivedLowerShriekOfCompactificationBaseChangeMap
          (ModuleCat.{u + 1} Λ) sq c).app N)).app
          (L((v)^*[ModuleCat.{u + 1} Λ]).obj P) ≫
      ((projectionMapOfCompactification (ModuleCat.{u + 1} Λ)
        (c.ofIsPullback sq)).app (L((w)^*[ModuleCat.{u + 1} Λ]).obj N)).app
          (L((v)^*[ModuleCat.{u + 1} Λ]).obj P)
```

## New

```lean
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat

theorem compactification_projection_exchange_coherence
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {T' T U' U : Scheme.{u}} {w : T' ⟶ T} {u' : T' ⟶ U'}
    {u : T ⟶ U} {v : U' ⟶ U}
    [IsSeparated u] [LocallyOfFiniteType u] [QuasiCompact u]
    (sq : IsPullback w u' u v) (c : Compactification u) [QuasiCompact c.i]
    (N : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} Λ)))
    (P : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} Λ))) :
    L((v)^*[ModuleCat.{u + 1} Λ]).map
        (((projectionMapOfCompactification (ModuleCat.{u + 1} Λ) c).app N).app P) ≫
      (rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat.{u + 1} Λ) sq c).app
        (((-⊗ᴸ-(T)[ModuleCat.{u + 1} Λ]).obj N).obj
          (L((u)^*[ModuleCat.{u + 1} Λ]).obj P)) ≫
      (Rf_!(c.ofIsPullback sq)[ModuleCat.{u + 1} Λ]).map
        (((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} Λ) w).app N).app
          (L((u)^*[ModuleCat.{u + 1} Λ]).obj P)) ≫
      (Rf_!(c.ofIsPullback sq)[ModuleCat.{u + 1} Λ]).map
        (((-⊗ᴸ-(T')[ModuleCat.{u + 1} Λ]).obj
          (L((w)^*[ModuleCat.{u + 1} Λ]).obj N)).map
            ((leftDerivedUpperStarSquareIso (ModuleCat.{u + 1} Λ) sq.toCommSq).inv.app P)) =
    ((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} Λ) v).app
        ((Rf_!(c)[ModuleCat.{u + 1} Λ]).obj N)).app P ≫
      ((-⊗ᴸ-(U')[ModuleCat.{u + 1} Λ]).map
        ((rightDerivedLowerShriekOfCompactificationBaseChangeMap
          (ModuleCat.{u + 1} Λ) sq c).app N)).app
          (L((v)^*[ModuleCat.{u + 1} Λ]).obj P) ≫
      ((projectionMapOfCompactification (ModuleCat.{u + 1} Λ)
        (c.ofIsPullback sq)).app (L((w)^*[ModuleCat.{u + 1} Λ]).obj N)).app
          (L((v)^*[ModuleCat.{u + 1} Λ]).obj P)
```

The theorem body is replaced by the complete proof. All newly introduced declarations are
private and have complete proofs or explicit canonical data. The dependency node's proof,
proof_deps and proof_origin are updated, and obsolete tool_uses entries are removed.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.CompactificationProjectionExchangeCoherence | T2 | Proof completed; public theorem signature unchanged. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed | No declaration use; no adaptation expected; proof-only helpers invisible. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | No declaration use; no adaptation expected; proof-only helpers invisible. |
| Sheaf.Paper.AdicPurityFiniteTensor | unclaimed | No declaration use; no adaptation expected; proof-only helpers invisible. |
| Sheaf.Paper.AdicPurityObjects | unclaimed | No declaration use; no adaptation expected; proof-only helpers invisible. |
| Sheaf.Paper.AdicPurityRootComparisons | unclaimed | No declaration use; no adaptation expected; proof-only helpers invisible. |
| Sheaf.Paper.AdicPuritySourceReduction | unclaimed | No declaration use; no adaptation expected; proof-only helpers invisible. |
| Sheaf.Paper.AdicPurityTwistReduction | unclaimed | No declaration use; no adaptation expected; proof-only helpers invisible. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | No declaration use; no adaptation expected; proof-only helpers invisible. |
| Sheaf.Paper.CohomologicalSmoothComposition | unclaimed | Compiled unchanged against the sandbox output; no adaptation needed. |
| Sheaf.Paper.CohomologicalSmoothnessTheorem | unclaimed | No declaration use; no adaptation expected; proof-only helpers invisible. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | No declaration use; no adaptation expected; proof-only helpers invisible. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed | No declaration use; no adaptation expected; proof-only helpers invisible. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | No declaration use; no adaptation expected; proof-only helpers invisible. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed | No declaration use; no adaptation expected; proof-only helpers invisible. |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed | No declaration use; no adaptation expected; proof-only helpers invisible. |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed | No declaration use; no adaptation expected; proof-only helpers invisible. |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed | No declaration use; no adaptation expected; proof-only helpers invisible. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | No declaration use; no adaptation expected; proof-only helpers invisible. |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed | No declaration use; no adaptation expected; proof-only helpers invisible. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed | No declaration use; no adaptation expected; proof-only helpers invisible. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | No declaration use; no adaptation expected; proof-only helpers invisible. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | No declaration use; no adaptation expected; proof-only helpers invisible. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | No declaration use; no adaptation expected; proof-only helpers invisible. |
| Sheaf.Paper.PurityDiagonalDualizingObject | unclaimed | No declaration use; no adaptation expected; proof-only helpers invisible. |
| Sheaf.Paper.PurityDiagonalSectionPasting | unclaimed | No declaration use; no adaptation expected; proof-only helpers invisible. |
| Sheaf.Paper.PurityDncFamilyIntrinsic | unclaimed | No declaration use; no adaptation expected; proof-only helpers invisible. |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | unclaimed | No declaration use; no adaptation expected; proof-only helpers invisible. |
| Sheaf.Paper.RationalSmoothPurityCanonical | unclaimed | No declaration use; no adaptation expected; proof-only helpers invisible. |
| Sheaf.Paper.SmoothPurityMap | unclaimed | No declaration use; no adaptation expected; proof-only helpers invisible. |
| Sheaf.Paper.SmoothTrace | unclaimed | No declaration use; no adaptation expected; proof-only helpers invisible. |
| Sheaf.Paper.TwistFrobeniusScalar | unclaimed | No declaration use; no adaptation expected; proof-only helpers invisible. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | No declaration use; no adaptation expected; proof-only helpers invisible. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | No declaration use; no adaptation expected; proof-only helpers invisible. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | No declaration use; no adaptation expected; proof-only helpers invisible. |

## Status

landed 20261020T211828-L-3508294 2026-10-20 (merge of deliver/T2/Sheaf.AlgebraicGeometry.CompactificationProjectionExchangeCoherence)
