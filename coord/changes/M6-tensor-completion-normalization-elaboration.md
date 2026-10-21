# WeilConjectures.ConstructibleTensorCompletionNormalized

## Reason

The presentation theorem is a direct repackaging of `constructibleTensorCompletion`.
Its normalization predicate made elaboration unfold the finite total tensor while
checking the type of its pure section. State that definitional conversion explicitly
by unfolding `integralOperationsTensorLevel` on the right-hand side. The resulting
section and all four clauses are definitionally equal to the original ones. No
mathematical hypothesis, equation, object, or comparison changes.

Local transparency settings keep the finite tensor sealed while elaborating this
predicate and its presentation proof. Additional local irreducibility attributes on
already typed functors before `At` avoid expensive unfolding of their definitions.
These attributes are local and export no change in reducibility. The full file
compiled in 55.7 seconds, with one original theorem still admitted.

## Old

```lean
def ConstructibleTensorCompletionNormalized
    (tensor : DerivedCategory (integralTowerModules l E W) ×
      DerivedCategory (integralTowerModules l E W) ⥤ DerivedCategory (integralTowerModules l E W))
    (model : ((integralOperationsGoodComplex l E W).ι.prod
        (integralOperationsGoodComplex l E W).ι) ⋙ constructibleTensorTotal l E W ⋙
          DerivedCategory.Q ≅
      ((integralOperationsGoodLocalization l E W).prod
        (integralOperationsGoodLocalization l E W)) ⋙ tensor)
    (cochain : constructibleTensorTotal l E W ⟶ integralOperationsTensorComplexFunctor l E W)
    (comparison : tensor ⟶ integralCompletedTensor l E W) : Prop :=
  (∀ (P Q : CochainComplex (integralTowerModules l E W) ℤ) (p q : ℤ) (n : ℕ)
    (U : W.ProEtᵒᵖ) (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
  (((cochain.app (P, Q) ≫ CochainComplex.mappingCocone.fst
    (constructibleTensorBoundary l E W P Q) ≫
    Pi.π (fun n ↦ (integralOperationsTensorLevel l E W n).obj (P, Q)) n).f
      (p + q)).val.app U)
    (constructibleTensorTotalSection l E W P Q p q U x y) =
    integralOperationsTotalTensorSection l E W n P Q p q U
      (unrestrictedIntegralTensorSection l E W n (P.X p) U 1 x)
      (unrestrictedIntegralTensorSection l E W n (Q.X q) U 1 y)) ∧
  (∀ (P Q : CochainComplex (integralTowerModules l E W) ℤ) (i j : ℤ)
    (h : i + -1 = j),
  (cochain.app (P, Q)).f i ≫ (CochainComplex.mappingCocone.snd
    (constructibleTensorBoundary l E W P Q)).v i j h = 0) ∧
  (∀ (P Q : (integralOperationsGoodComplex l E W).FullSubcategory),
  model.hom.app (P, Q) ≫ comparison.app (DerivedCategory.Q.obj P.obj,
      DerivedCategory.Q.obj Q.obj) ≫
    (integralCompletedTensorComparison l E W).hom.app (P, Q) =
    DerivedCategory.Q.map (cochain.app (P.obj, Q.obj))) ∧
  (∀ M N : DerivedCategory (integralTowerModules l E W),
  sfIntegralConstructible l E W M → sfIntegralConstructible l E W N →
    IsDerivedCompleteUnrestricted l E W (tensor.obj (M, N)) ∧ IsIso (comparison.app (M, N)))
```

## New

```lean
def ConstructibleTensorCompletionNormalized
    (tensor : DerivedCategory (integralTowerModules l E W) ×
      DerivedCategory (integralTowerModules l E W) ⥤ DerivedCategory (integralTowerModules l E W))
    (model : ((integralOperationsGoodComplex l E W).ι.prod
        (integralOperationsGoodComplex l E W).ι) ⋙ constructibleTensorTotal l E W ⋙
          DerivedCategory.Q ≅
      ((integralOperationsGoodLocalization l E W).prod
        (integralOperationsGoodLocalization l E W)) ⋙ tensor)
    (cochain : constructibleTensorTotal l E W ⟶ integralOperationsTensorComplexFunctor l E W)
    (comparison : tensor ⟶ integralCompletedTensor l E W) : Prop :=
  (∀ (P Q : CochainComplex (integralTowerModules l E W) ℤ) (p q : ℤ) (n : ℕ)
    (U : W.ProEtᵒᵖ) (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
  (((cochain.app (P, Q) ≫ CochainComplex.mappingCocone.fst
    (constructibleTensorBoundary l E W P Q) ≫
    Pi.π (fun n ↦ (integralOperationsTensorLevel l E W n).obj (P, Q)) n).f
      (p + q)).val.app U)
    (constructibleTensorTotalSection l E W P Q p q U x y) =
    (by
      unfold integralOperationsTensorLevel
      exact integralOperationsTotalTensorSection l E W n P Q p q U
        (unrestrictedIntegralTensorSection l E W n (P.X p) U 1 x)
        (unrestrictedIntegralTensorSection l E W n (Q.X q) U 1 y))) ∧
  (∀ (P Q : CochainComplex (integralTowerModules l E W) ℤ) (i j : ℤ)
    (h : i + -1 = j),
  (cochain.app (P, Q)).f i ≫ (CochainComplex.mappingCocone.snd
    (constructibleTensorBoundary l E W P Q)).v i j h = 0) ∧
  (∀ (P Q : (integralOperationsGoodComplex l E W).FullSubcategory),
  model.hom.app (P, Q) ≫ comparison.app (DerivedCategory.Q.obj P.obj,
      DerivedCategory.Q.obj Q.obj) ≫
    (integralCompletedTensorComparison l E W).hom.app (P, Q) =
    DerivedCategory.Q.map (cochain.app (P.obj, Q.obj))) ∧
  (∀ M N : DerivedCategory (integralTowerModules l E W),
  sfIntegralConstructible l E W M → sfIntegralConstructible l E W N →
    IsDerivedCompleteUnrestricted l E W (tensor.obj (M, N)) ∧ IsIso (comparison.app (M, N)))
```

## Users

`tools/downstream.py Sheaf.Paper.RationalRealizationTensorComparison
--uses ConstructibleTensorCompletionNormalized --names` found no downstream modules.
A repository search found only this module's declaration and internal uses. The
presentation field and `completionIso` use the same four normalization clauses.
No consumer adaptation or target-statement edit is required.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.RationalRealizationTensorComparison | M6 | Same definition up to reduction; presentation theorem proved; local elaboration settings only. |

## Status

landed 20261021T163813-L-1098808 2026-10-21 (merge of deliver/M6/Sheaf.Paper.RationalRealizationTensorComparison)
