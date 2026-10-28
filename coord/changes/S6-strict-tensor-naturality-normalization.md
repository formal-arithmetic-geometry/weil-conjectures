# WeilConjectures.podReindexingStrictTensorTowersNaturality

## Reason

The earlier statement omitted normalization of D.quotient. The structure gives objectwise isomorphisms, not a natural family. For identity reindexing, multiplying the quotient isomorphism for one nonzero good representative by -1, and its tensor comparison by the product of the two signs, preserves the stated generator formula and tower compatibility but need not preserve a morphism between two representatives. For odd residue characteristic, a nonzero inclusion between finite free representatives detects the failure. The source uses the fixed normalized quotient comparison. Add only its existing QuotientGenerators law; the parent already assumes all Laws. No target or parent statement changes.

## Old

```lean
theorem podReindexingStrictTensorTowersNaturality
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) 
    (τ : ∀ P Q : (integralOperationsGoodComplex l E Y).FullSubcategory,
        (podReindexTower l E g).obj
            ((integralOperationsTensorTowerFunctor l E Y).obj (P.obj,Q.obj)) ≅
          (integralOperationsTensorTowerFunctor l E X).obj
            (((podGoodReindex l E g D).obj P).obj,((podGoodReindex l E g D).obj Q).obj))
    (hgen : ∀ (P Q : (integralOperationsGoodComplex l E Y).FullSubcategory)
        (n : ℕ) (p q : ℤ) (U : X.ProEt)
        (x : (((unrestrictedIntegralFiniteComplex l E Y n).obj P.obj).X p).val.obj
          (op ((proEtaleIsoPostcompose g).obj U)))
        (y : (((unrestrictedIntegralFiniteComplex l E Y n).obj Q.obj).X q).val.obj
          (op ((proEtaleIsoPostcompose g).obj U))),
        ((((τ P Q).hom.app (op n)).f (p + q)).val.app (op U))
            (integralOperationsTotalTensorSection l E Y n P.obj Q.obj p q
              (op ((proEtaleIsoPostcompose g).obj U)) x y) =
          integralOperationsTotalTensorSection l E X n
            (((podGoodReindex l E g D).obj P).obj) (((podGoodReindex l E g D).obj Q).obj)
            p q (op U) ((((D.quotient P.obj P.property n).hom.f p).val.app (op U)) x)
              ((((D.quotient Q.obj Q.property n).hom.f q).val.app (op U)) y)) :
      ∀ (P Q P' Q' : (integralOperationsGoodComplex l E Y).FullSubcategory)
        (a : P ⟶ P') (b : Q ⟶ Q'),
        (podReindexTower l E g).map
            ((integralOperationsTensorTowerFunctor l E Y).map (Prod.mkHom a.hom b.hom)) ≫
            (τ P' Q').hom =
          (τ P Q).hom ≫ (integralOperationsTensorTowerFunctor l E X).map
            (Prod.mkHom ((podGoodReindex l E g D).map a).hom
              ((podGoodReindex l E g D).map b).hom)
```

## New

```lean
theorem podReindexingStrictTensorTowersNaturality
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (hD : PodCompletionReindex.QuotientGenerators l E g D)
    (τ : ∀ P Q : (integralOperationsGoodComplex l E Y).FullSubcategory,
        (podReindexTower l E g).obj
            ((integralOperationsTensorTowerFunctor l E Y).obj (P.obj,Q.obj)) ≅
          (integralOperationsTensorTowerFunctor l E X).obj
            (((podGoodReindex l E g D).obj P).obj,((podGoodReindex l E g D).obj Q).obj))
    (hgen : ∀ (P Q : (integralOperationsGoodComplex l E Y).FullSubcategory)
        (n : ℕ) (p q : ℤ) (U : X.ProEt)
        (x : (((unrestrictedIntegralFiniteComplex l E Y n).obj P.obj).X p).val.obj
          (op ((proEtaleIsoPostcompose g).obj U)))
        (y : (((unrestrictedIntegralFiniteComplex l E Y n).obj Q.obj).X q).val.obj
          (op ((proEtaleIsoPostcompose g).obj U))),
        ((((τ P Q).hom.app (op n)).f (p + q)).val.app (op U))
            (integralOperationsTotalTensorSection l E Y n P.obj Q.obj p q
              (op ((proEtaleIsoPostcompose g).obj U)) x y) =
          integralOperationsTotalTensorSection l E X n
            (((podGoodReindex l E g D).obj P).obj) (((podGoodReindex l E g D).obj Q).obj)
            p q (op U) ((((D.quotient P.obj P.property n).hom.f p).val.app (op U)) x)
              ((((D.quotient Q.obj Q.property n).hom.f q).val.app (op U)) y)) :
      ∀ (P Q P' Q' : (integralOperationsGoodComplex l E Y).FullSubcategory)
        (a : P ⟶ P') (b : Q ⟶ Q'),
        (podReindexTower l E g).map
            ((integralOperationsTensorTowerFunctor l E Y).map (Prod.mkHom a.hom b.hom)) ≫
            (τ P' Q').hom =
          (τ P Q).hom ≫ (integralOperationsTensorTowerFunctor l E X).map
            (Prod.mkHom ((podGoodReindex l E g D).map a).hom
              ((podGoodReindex l E g D).map b).hom)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.PodReindexingStrictTensorTowersNaturality | S6 | Add the missing quotient normalization hypothesis and prove the corrected theorem. |
| Sheaf.Paper.PodReindexingStrictTensorTowers | unclaimed | Pass its existing quotient normalization law; statement unchanged. |

The source-only downstream audit finds these two declaration mentions. Other downstream modules do not use the changed declaration directly. No definition used by Challenge.lean changes.

## Status

landed 20261028T055755-L-807528 2026-10-28 (merge of deliver/S6/Sheaf.Paper.PodReindexingStrictTensorTowersNaturality)
