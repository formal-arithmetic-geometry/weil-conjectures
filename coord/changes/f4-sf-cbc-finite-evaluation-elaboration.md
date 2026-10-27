# AlgebraicGeometry.Scheme.sfCbcFiniteEvaluationIso

## Reason

Name the transported complex and share its flatness proof while retaining the
original composite and its association. The transported complex has its
constant-coefficient type stated explicitly.

This is an elaboration refactor: the old and new bodies are judgmentally equal
(after expanding local bindings and ignoring proof arguments by proof irrelevance). No ordinary, derived, quotient, completion, or
evaluation map is replaced. No hypothesis or conclusion changes. The refactored
definitions do not occur in any target statement in `lean/Challenge.lean`; target
signatures and their meanings stay unchanged. The independent reader should
verify judgmental equality as part of reviewing the definition change.

## Old

```lean
def sfCbcFiniteEvaluationIso (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : CompleteCoefficientDatum A) {K : proEtaleDerivedCategory X A}
    (M : AdicKFlatModel X A K) (n : ℕ) :
    (sfCbcEvaluate X A n).obj ((sfCbcReduction X d).obj K) ≅
      (sfCbcModelDerived X A).functor.obj
        (adicReductionUnderlying X d M ⟨n + 1, Nat.succ_pos n⟩) :=
  (sfCbcEvaluate X A n).mapIso
    ((sfCbcQuotientPresentation X d).tower.mapIso
      ((sfCbcModelDerived X A).functor.mapIso M.realization.symm ≪≫
        (sfCbcModelDerivedFactors X A).app M.complex) ≪≫
      @asIso _ _ _ _ ((sfCbcQuotientPresentation X d).comparison.app
        (((sfCbcModelModules X A).mapHomologicalComplex (.up ℤ)).obj M.complex))
        ((sfCbcQuotientPresentation X d).laws.2.1 _
          (sfCbcModelComplex_kflat X M).1 (sfCbcModelComplex_kflat X M).2)) ≪≫
    (sfCbcEvaluateFactors X A n).app
      (ConstantCompletion.reductionComplex (proEtaleModelTopology X)
        (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false
          (((sfCbcModelModules X A).mapHomologicalComplex (.up ℤ)).obj M.complex)) ≪≫
    (ConstantCompletion.Q (sfCbcModelRing X A)).mapIso
      (sfCbcFiniteModelIso_existsUnique X d M n).exists.choose ≪≫
    sfCbcFiniteModelFactors X d M n
```

## New

```lean
def sfCbcFiniteEvaluationIso (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : CompleteCoefficientDatum A) {K : proEtaleDerivedCategory X A}
    (M : AdicKFlatModel X A K) (n : ℕ) :
    (sfCbcEvaluate X A n).obj ((sfCbcReduction X d).obj K) ≅
      (sfCbcModelDerived X A).functor.obj
        (adicReductionUnderlying X d M ⟨n + 1, Nat.succ_pos n⟩) := by
  let P : ConstantCompletion.Cx (sfCbcModelRing X A) :=
    ((sfCbcModelModules X A).mapHomologicalComplex (.up ℤ)).obj M.complex
  have hP := sfCbcModelComplex_kflat X M
  exact (sfCbcEvaluate X A n).mapIso
    ((sfCbcQuotientPresentation X d).tower.mapIso
      ((sfCbcModelDerived X A).functor.mapIso M.realization.symm ≪≫
        (sfCbcModelDerivedFactors X A).app M.complex) ≪≫
      @asIso _ _ _ _ ((sfCbcQuotientPresentation X d).comparison.app P)
        ((sfCbcQuotientPresentation X d).laws.2.1 P hP.1 hP.2)) ≪≫
    (sfCbcEvaluateFactors X A n).app
      (ConstantCompletion.reductionComplex (proEtaleModelTopology X)
        (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false P) ≪≫
    (ConstantCompletion.Q (sfCbcModelRing X A)).mapIso
      (sfCbcFiniteModelIso_existsUnique X d M n).exists.choose ≪≫
    sfCbcFiniteModelFactors X d M n
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
