# integralPullEvaluation_cochainSquare_component_core_expanded

## Reason

Complete the assigned proof via the direct-image transition square and adjunction mates.
The added attributes in the item are local reducibility settings; the existing public
statement and public imports stay unchanged. The new helper module and its proved
public theorem are recorded by the new DAG node. No existing public definition,
instance or attribute changes, and no consumer adaptation is needed.

## Old

```lean
theorem integralPullEvaluation_cochainSquare_component_core_expanded
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (r₀ : normalizedDVRModuleRes l E X (Nat.le_succ n) ⋙
        proEtaleConstantModuleDirectImage f (Padic.coefficientExtensionRing l E (n + 2)) ≅
      proEtaleConstantModuleDirectImage f (Padic.coefficientExtensionRing l E (n + 1)) ⋙
        normalizedDVRModuleRes l E Y (Nat.le_succ n))
    (hr₀ : HEq r₀ (proEtaleCoefficientDirectImageComparison f
      (Padic.coefficientExtensionTransition l E (n + 1))).symm)
    (P : CochainComplex (coefficientSequenceModules l E Y) ℤ) (i : ℤ) :
    ((NatTrans.mapHomologicalComplex
        (coefficientSequenceTransition l E X (Nat.le_succ n)) (.up ℤ)).app
        (((pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ)).obj P)).f i ≫
      (((normalizedDVRModuleRes l E X (Nat.le_succ n)).mapHomologicalComplex (.up ℤ)).map
        (((pullbackTensorInverseEvaluationComplex l E f n).symm ≪≫
    Functor.isoWhiskerLeft
      ((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ))
      (NatIso.mapHomologicalComplex (pullbackTensorLevelIntrinsic l E f n)
        (.up ℤ))).hom.app P)).f i =
    ((((pullbackTensorInverseEvaluationComplex l E f (n + 1)).symm ≪≫
    Functor.isoWhiskerLeft
      ((coefficientSequenceEvaluation l E Y (n + 1)).mapHomologicalComplex (.up ℤ))
      (NatIso.mapHomologicalComplex (pullbackTensorLevelIntrinsic l E f (n + 1))
        (.up ℤ))).hom.app P)).f i ≫
      (((sfIntrinsicPullback (finiteCoefficientRing l E (n + 2)) f).mapHomologicalComplex
        (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex
          (coefficientSequenceTransition l E Y (Nat.le_succ n)) (.up ℤ)).app P)).f i ≫
      ((NatTrans.mapHomologicalComplex
        ((mateEquiv
            (sfIntrinsicConstantModuleAdjunction f (finiteCoefficientRing l E (n + 1)))
            (sfIntrinsicConstantModuleAdjunction f (finiteCoefficientRing l E (n + 2)))).symm
          (TwoSquare.mk _ _ _ _ r₀.inv)).natTrans (.up ℤ)).app
        (((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj P)).f i
```

## New

```lean
theorem integralPullEvaluation_cochainSquare_component_core_expanded
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (r₀ : normalizedDVRModuleRes l E X (Nat.le_succ n) ⋙
        proEtaleConstantModuleDirectImage f (Padic.coefficientExtensionRing l E (n + 2)) ≅
      proEtaleConstantModuleDirectImage f (Padic.coefficientExtensionRing l E (n + 1)) ⋙
        normalizedDVRModuleRes l E Y (Nat.le_succ n))
    (hr₀ : HEq r₀ (proEtaleCoefficientDirectImageComparison f
      (Padic.coefficientExtensionTransition l E (n + 1))).symm)
    (P : CochainComplex (coefficientSequenceModules l E Y) ℤ) (i : ℤ) :
    ((NatTrans.mapHomologicalComplex
        (coefficientSequenceTransition l E X (Nat.le_succ n)) (.up ℤ)).app
        (((pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ)).obj P)).f i ≫
      (((normalizedDVRModuleRes l E X (Nat.le_succ n)).mapHomologicalComplex (.up ℤ)).map
        (((pullbackTensorInverseEvaluationComplex l E f n).symm ≪≫
    Functor.isoWhiskerLeft
      ((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ))
      (NatIso.mapHomologicalComplex (pullbackTensorLevelIntrinsic l E f n)
        (.up ℤ))).hom.app P)).f i =
    ((((pullbackTensorInverseEvaluationComplex l E f (n + 1)).symm ≪≫
    Functor.isoWhiskerLeft
      ((coefficientSequenceEvaluation l E Y (n + 1)).mapHomologicalComplex (.up ℤ))
      (NatIso.mapHomologicalComplex (pullbackTensorLevelIntrinsic l E f (n + 1))
        (.up ℤ))).hom.app P)).f i ≫
      (((sfIntrinsicPullback (finiteCoefficientRing l E (n + 2)) f).mapHomologicalComplex
        (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex
          (coefficientSequenceTransition l E Y (Nat.le_succ n)) (.up ℤ)).app P)).f i ≫
      ((NatTrans.mapHomologicalComplex
        ((mateEquiv
            (sfIntrinsicConstantModuleAdjunction f (finiteCoefficientRing l E (n + 1)))
            (sfIntrinsicConstantModuleAdjunction f (finiteCoefficientRing l E (n + 2)))).symm
          (TwoSquare.mk _ _ _ _ r₀.inv)).natTrans (.up ℤ)).app
        (((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj P)).f i
```

The proof is now complete. Its proof-only import is
`Sheaf.SixFunctors.IntegralPullEvaluationDirectTransitionSquare`, whose sole public
theorem is `WeilConjectures.IntegralSystemRealization.integralPullEvaluation_directTransitionSquare`.
It adds no instance or global attribute.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.IntegralPullEvaluationCochainSquareComponentCore | G9 | Assigned proof completed; signature and public imports preserved. |
| Sheaf.SixFunctors.IntegralPullEvaluationDirectTransitionSquare | G9 (new module) | New proved helper with a DAG node. |
| Sheaf.SixFunctors.IntegralPullEvaluationCochainSquareComponent | Unclaimed in shared snapshot | Sole direct importer; compiled unchanged against the delivery. |

## Status

landed 20261028T055658-L-794948 2026-10-28 (merge of deliver/G9/Sheaf.SixFunctors.IntegralPullEvaluationCochainSquareComponentCore)
