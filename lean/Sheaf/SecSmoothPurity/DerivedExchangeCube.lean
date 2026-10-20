/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W2
-/
module

public import WeilConjectures.SixFunctors.BaseChange.Derived
import WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Horizontal

/-! # Coherence of derived exchange around a commutative cube -/

@[expose] public section

universe u


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Etale

set_option autoImplicit false

-- Horizontal pasting with specified diagonals, evaluated at an arbitrary complex.
private lemma pasteHoriz
    {X'' X' X Y'' Y' Y : Scheme.{u}}
    {g'' : X'' ⟶ X'} {g' : X' ⟶ X} {f'' : X'' ⟶ Y''}
    {f' : X' ⟶ Y'} {f : X ⟶ Y} {h : Y'' ⟶ Y'} {g : Y' ⟶ Y}
    (sq₁ : CommSq g' f' f g) (sq₂ : CommSq g'' f'' f' h)
    (top : X'' ⟶ X) (bottom : Y'' ⟶ Y)
    (ht : top = g'' ≫ g') (hb : bottom = h ≫ g)
    (sq : CommSq top f'' f bottom)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq).app K =
      (upperStarCompDerivedPlus AddCommGrpCat.{u + 1} h g bottom hb).hom.app
          ((lowerStar AddCommGrpCat.{u + 1} f).rightDerivedFunctorPlus.obj K) ≫
        (upperStar AddCommGrpCat.{u + 1} h).mapDerivedCategoryPlus.map
          ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq₁).app K) ≫
        (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq₂).app
          ((upperStar AddCommGrpCat.{u + 1} g').mapDerivedCategoryPlus.obj K) ≫
        (lowerStar AddCommGrpCat.{u + 1} f'').rightDerivedFunctorPlus.map
          ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1} g'' g' top ht).inv.app K) := by
  subst top bottom
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.comp_obj,
    Category.id_comp] using
      NatTrans.congr_app
        (derivedBaseChangeMapPlus_paste_horiz AddCommGrpCat.{u + 1} sq₁ sq₂ sq) K

/-- The four derived exchange maps in a commutative cube satisfy the canonical
cube-pasting identity.  This is the statement corresponding to the two
possible mate pastings; the proof is supplied at a later stage.

Source: Stacks Project, `sites-cohomology.tex`, Tags 0E47 and 07A7; the
canonical-map verification in Tag 0EZT (blueprint: lem-kun-derived-exchange-cube). -/
theorem derivedExchangeCube
    {X₀ Y₀ S₀ T₀ X₁ Y₁ S₁ T₁ : Scheme.{u}}
    (h₀ : Y₀ ⟶ X₀) (e₀ : Y₀ ⟶ T₀) (f₀ : X₀ ⟶ S₀) (g₀ : T₀ ⟶ S₀)
    (h₁ : Y₁ ⟶ X₁) (e₁ : Y₁ ⟶ T₁) (f₁ : X₁ ⟶ S₁) (g₁ : T₁ ⟶ S₁)
    (h₀e₀ : h₀ ≫ f₀ = e₀ ≫ g₀) (h₁e₁ : h₁ ≫ f₁ = e₁ ≫ g₁)
    (x : X₁ ⟶ X₀) (y : Y₁ ⟶ Y₀) (s : S₁ ⟶ S₀) (a : T₁ ⟶ T₀)
    (f₀x : x ≫ f₀ = f₁ ≫ s) (g₀a : a ≫ g₀ = g₁ ≫ s)
    (h₀y : y ≫ h₀ = h₁ ≫ x) (e₀y : y ≫ e₀ = e₁ ≫ a) :
    let A := AddCommGrpCat.{u + 1}
    let E₀ := derivedBaseChangeMapPlus A (CommSq.mk h₀e₀.symm)
    let E₁ := derivedBaseChangeMapPlus A (CommSq.mk h₁e₁.symm)
    let P := derivedBaseChangeMapPlus A (CommSq.mk g₀a)
    let Q := derivedBaseChangeMapPlus A (CommSq.mk h₀y)
    let α :=
      (upperStarCompDerivedPlus A x f₀ (x ≫ f₀) rfl).symm ≪≫
        (eqToIso (by rw [f₀x])) ≪≫
          upperStarCompDerivedPlus A f₁ s (x ≫ f₀) f₀x
    let β :=
      (upperStarCompDerivedPlus A y e₀ (y ≫ e₀) rfl).symm ≪≫
        (eqToIso (by rw [e₀y])) ≪≫
          upperStarCompDerivedPlus A e₁ a (y ≫ e₀) e₀y
    Functor.whiskerLeft (lowerStar A g₀).rightDerivedFunctorPlus α.hom ≫
          Functor.whiskerRight P (upperStar A f₁).mapDerivedCategoryPlus ≫
          Functor.whiskerLeft (upperStar A a).mapDerivedCategoryPlus E₁ =
      Functor.whiskerRight E₀ (upperStar A x).mapDerivedCategoryPlus ≫
          Functor.whiskerLeft (upperStar A e₀).mapDerivedCategoryPlus Q ≫
          Functor.whiskerRight β.hom (lowerStar A h₁).rightDerivedFunctorPlus := by
  dsimp only
  let outer : CommSq (y ≫ e₀) h₁ g₀ (x ≫ f₀) := ⟨by
    rw [Category.assoc, ← h₀e₀, ← Category.assoc, h₀y, Category.assoc]⟩
  apply NatTrans.ext
  funext K
  have hp₀ := pasteHoriz (CommSq.mk h₀e₀.symm) (CommSq.mk h₀y)
    (y ≫ e₀) (x ≫ f₀) rfl rfl outer K
  have hp₁ := pasteHoriz (CommSq.mk g₀a) (CommSq.mk h₁e₁.symm)
    (y ≫ e₀) (x ≫ f₀) e₀y f₀x outer K
  have hp := hp₁.symm.trans hp₀
  have hw := congrArg (fun m ↦
    (upperStarCompDerivedPlus AddCommGrpCat.{u + 1} x f₀).inv.app
        ((lowerStar AddCommGrpCat.{u + 1} g₀).rightDerivedFunctorPlus.obj K) ≫ m ≫
      (lowerStar AddCommGrpCat.{u + 1} h₁).rightDerivedFunctorPlus.map
        ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1} e₁ a (y ≫ e₀) e₀y).hom.app K)) hp
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
    Iso.inv_hom_id_app_assoc] at hw
  simpa using hw

end AlgebraicGeometry.Etale
