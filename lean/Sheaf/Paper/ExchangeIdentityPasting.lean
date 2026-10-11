/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
import Sheaf.AlgebraicGeometry.DerivedDirectImageComposition
import WeilConjectures.SixFunctors.BaseChange.Derived

/-! # Identity and pasting equations for exchange

Source: Stacks Project, Remarks 07A7, 0E46, 0E47 and Lemma 0D6E;
blueprint node order 1044 (blueprint: lem-weil-pbc-exchange-identity-pasting).
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- Identity, horizontal-pasting, and vertical-pasting laws for the derived exchange map.

Source: Stacks Project, Remarks 07A7, 0E46, 0E47 and Lemma 0D6E
(blueprint: lem-weil-pbc-exchange-identity-pasting).

Proof, following the four steps of the node:
1. The source identification baseChange_eq_derivedBaseChangeMapPlus identifies
   derivedBaseChangeMapPlus with the mate of def-weil-pbc-derived-exchange.
   Thus exchange is the mate of the derived square
   comparison for the adjunctions of prop-weil-pbc-derived-inverse-image-adjunction.
2. For the identity square, lem-weil-pbc-derived-square-iso-pasting expresses the
   comparison using the identity isomorphisms of
   lem-weil-pbc-derived-inverse-image-composition. Apply lem-weil-pbc-mate-whisker
   and the identity conjugate law of lem-weil-pbc-mate-pasting to obtain exchange
   as the identity of Rf_* conjugated by these identity isomorphisms.
3. For horizontal pasting, lem-weil-pbc-cartesian-square-pasting gives the outer
   pullback. Its comparison is the pasted comparison conjugated by cD, by
   lem-weil-pbc-derived-square-iso-pasting. Apply lem-weil-pbc-mate-pasting (1)
   and lem-weil-pbc-mate-whisker to obtain the two exchanges conjugated by cD.
4. For vertical pasting, the same pullback-pasting and square-comparison laws
   give a square for composite adjunctions. Apply lem-weil-pbc-mate-pasting (2)
   to obtain its mate, the pasted exchanges. Change the two adjunctions using
   lem-weil-pbc-mate-pasting (3); the conjugates of cD are precisely the
   comparisons dD of def-weil-pbc-derived-direct-image-composition. Conjugation
   preserves inverses (def-weil-pbc-adjunction-conjugate), giving the equation.
-/
theorem derivedExchange_identity_pasting :
    let A := AddCommGrpCat.{u + 1}
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
      derivedBaseChangeMapPlus A (IsPullback.id_horiz f).toCommSq =
        Functor.whiskerLeft (f)_*[A].rightDerivedFunctorPlus
            (upperStarIdDerivedPlus A Y).hom ≫
          (Functor.rightUnitor _).hom ≫ (Functor.leftUnitor _).inv ≫
          Functor.whiskerRight (upperStarIdDerivedPlus A X).inv
            (f)_*[A].rightDerivedFunctorPlus)
    ∧ (∀ {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
        {f : X ⟶ Y} {g : Y' ⟶ Y}
        (sq₁ : IsPullback g' f' f g)
        {Y'' X'' : Scheme.{u}} {h : Y'' ⟶ Y'} {h' : X'' ⟶ X'}
        {f'' : X'' ⟶ Y''}
        (sq₂ : IsPullback h' f'' f' h),
      derivedBaseChangeMapPlus A (sq₂.paste_horiz sq₁).toCommSq =
        Functor.whiskerLeft (f)_*[A].rightDerivedFunctorPlus
            (upperStarCompDerivedPlus A h g).hom ≫
          (Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (derivedBaseChangeMapPlus A sq₁.toCommSq)
            (h)^*[A].mapDerivedCategoryPlus ≫
          (Functor.associator _ _ _).hom ≫
          Functor.whiskerLeft (g')^*[A].mapDerivedCategoryPlus
            (derivedBaseChangeMapPlus A sq₂.toCommSq) ≫
          (Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (upperStarCompDerivedPlus A h' g').inv
            (f'')_*[A].rightDerivedFunctorPlus)
    ∧ (∀ {X' X Y' Y Z' Z : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
        {f : X ⟶ Y} {g : Y' ⟶ Y} {e' : Y' ⟶ Z'} {e : Y ⟶ Z}
        {k : Z' ⟶ Z}
        (sq₁ : IsPullback g' f' f g) (sq₂ : IsPullback g e' e k),
      derivedBaseChangeMapPlus A (sq₁.paste_vert sq₂).toCommSq =
        Functor.whiskerRight
            (derivedDirectImageComposition e f).hom (k)^*[A].mapDerivedCategoryPlus ≫
          (Functor.associator _ _ _).hom ≫
          Functor.whiskerLeft (f)_*[A].rightDerivedFunctorPlus
            (derivedBaseChangeMapPlus A sq₂.toCommSq) ≫
          (Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (derivedBaseChangeMapPlus A sq₁.toCommSq)
            (e')_*[A].rightDerivedFunctorPlus ≫
          (Functor.associator _ _ _).hom ≫
          Functor.whiskerLeft (g')^*[A].mapDerivedCategoryPlus
            (derivedDirectImageComposition e' f').inv) := by
  sorry

end AlgebraicGeometry.Etale
