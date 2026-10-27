# AlgebraicGeometry.Scheme.sfCbcEvaluateExtensionIso

## Reason

Use Mathlib's whiskeringRightCompEvaluation in place of a concrete functor reflexivity conversion. That existing definition is exactly the same reflexivity isomorphism at the abstract functor level.

This is an elaboration refactor: the old and new bodies are judgmentally equal
(after expanding local bindings and Mathlib's named identity and ignoring proof
arguments by proof irrelevance). No ordinary, derived, quotient, completion, or
evaluation map is replaced. No hypothesis or conclusion changes. The refactored
definitions do not occur in any target statement in `lean/Challenge.lean`; target
signatures and their meanings stay unchanged. The independent reader should
verify judgmental equality as part of reviewing the definition change.

## Old

```lean
def sfCbcEvaluateExtensionIso {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]
    (A : Type t) [CommRing A] (n : ℕ) :
    sfCbcDerivedTowerExtension j A ⋙ sfCbcEvaluate X A n ≅
      sfCbcEvaluate U A n ⋙ sfCbcModelDerivedExtension j A :=
  (Functor.mapDerivedCategoryCompIso (sfCbcTowerExtension j A)
    (sfCbcEvaluateModule X A n)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (Iso.refl _) ≪≫
      Functor.mapDerivedCategoryCompIso (sfCbcEvaluateModule U A n)
        (sfCbcModelExtension j A)
```

## New

```lean
def sfCbcEvaluateExtensionIso {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]
    (A : Type t) [CommRing A] (n : ℕ) :
    sfCbcDerivedTowerExtension j A ⋙ sfCbcEvaluate X A n ≅
      sfCbcEvaluate U A n ⋙ sfCbcModelDerivedExtension j A :=
  (Functor.mapDerivedCategoryCompIso (sfCbcTowerExtension j A)
    (sfCbcEvaluateModule X A n)).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (whiskeringRightCompEvaluation (sfCbcModelExtension j A) (op n)) ≪≫
      Functor.mapDerivedCategoryCompIso (sfCbcEvaluateModule U A n)
        (sfCbcModelExtension j A)
```

## Users

`tools/downstream.py Sheaf.Paper.SfCbcExtensionZeroCompletion --uses
sfCbcTensorComparisonNormalized sfCbcFiniteEvaluationIso sfCbcEvaluateExtensionIso`
found 32 downstream modules and no external direct uses of these declarations.
All downstream modules are listed below; no consumer file is changed. The item's
normalization and evaluation statements still elaborate against these definitions.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.SfCbcExtensionZeroCompletion | F4 | Internal consumer; statement and maps unchanged. |
| Sheaf.Paper.CompactSupportLimitEquationData | unclaimed | No direct use; no adaptation needed. |
| Sheaf.Paper.CompactSupportLimitEquationRealization | unclaimed | No direct use; no adaptation needed. |
| Sheaf.Paper.CompactSupportPathReductionSquare | unclaimed | No direct use; no adaptation needed. |
| Sheaf.Paper.CompactSupportRealizationFactorNormalization | unclaimed | No direct use; no adaptation needed. |
| Sheaf.Paper.CompactSupportRealizationFactorization | unclaimed | No direct use; no adaptation needed. |
| Sheaf.Paper.CompactifiedTowerComparisons | unclaimed | No direct use; no adaptation needed. |
| Sheaf.Paper.CompleteIntegralConstantRestriction | unclaimed | No direct use; no adaptation needed. |
| Sheaf.Paper.CompletedSupportExchangeReduction | unclaimed | No direct use; no adaptation needed. |
| Sheaf.Paper.CompletedSupportIntermediateTower | unclaimed | No direct use; no adaptation needed. |
| Sheaf.Paper.CompletedSupportIntermediateTowerCore | unclaimed | No direct use; no adaptation needed. |
| Sheaf.Paper.CondensedOpenCoefficientModels | unclaimed | No direct use; no adaptation needed. |
| Sheaf.Paper.CondensedOpenCounitComparisons | unclaimed | No direct use; no adaptation needed. |
| Sheaf.Paper.CondensedOpenCounitRealization | unclaimed | No direct use; no adaptation needed. |
| Sheaf.Paper.CondensedOpenCounitRealizationSupport | unclaimed | No direct use; no adaptation needed. |
| Sheaf.Paper.CondensedOpenCounitUnits | unclaimed | No direct use; no adaptation needed. |
| Sheaf.Paper.CondensedOpenUnitComparison | unclaimed | No direct use; no adaptation needed. |
| Sheaf.Paper.NativeWeilScalarFrobeniusCounit | unclaimed | No direct use; no adaptation needed. |
| Sheaf.Paper.SfCbcCompactSupportCompositionLimit | unclaimed | No direct use; no adaptation needed. |
| Sheaf.SixFunctors.ConstantOpenRestrictionModelComparison | unclaimed | No direct use; no adaptation needed. |
| Sheaf.SixFunctors.ConstantOrdinaryCompactificationComparison | unclaimed | No direct use; no adaptation needed. |
| Sheaf.SixFunctors.ConstantScalarQuotientComparison | unclaimed | No direct use; no adaptation needed. |
| Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison | unclaimed | No direct use; no adaptation needed. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeCoordinates | unclaimed | No direct use; no adaptation needed. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeOrdinaryCoordinates | unclaimed | No direct use; no adaptation needed. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeWords | unclaimed | No direct use; no adaptation needed. |
| Sheaf.SixFunctors.IntegralCompactificationComparisonBridge | unclaimed | No direct use; no adaptation needed. |
| Sheaf.SixFunctors.IntegralCompactificationComparisonData | unclaimed | No direct use; no adaptation needed. |
| Sheaf.SixFunctors.IntegralCompactificationOrdinaryScalarAction | unclaimed | No direct use; no adaptation needed. |
| Sheaf.SixFunctors.IntegralConstantCompleteTransport | unclaimed | No direct use; no adaptation needed. |
| Sheaf.SixFunctors.IntegralConstantCompleteTransportComplete | unclaimed | No direct use; no adaptation needed. |
| Sheaf.SixFunctors.IntegralConstantCompleteTransportHom | unclaimed | No direct use; no adaptation needed. |
| Sheaf.SixFunctors.SemilinearOrdinaryCompactificationComparison | unclaimed | No direct use; no adaptation needed. |

## Status

landed 20261026T065626-L-3135916 2026-10-26 (merge of deliver/F4/Sheaf.Paper.SfCbcExtensionZeroCompletion)
