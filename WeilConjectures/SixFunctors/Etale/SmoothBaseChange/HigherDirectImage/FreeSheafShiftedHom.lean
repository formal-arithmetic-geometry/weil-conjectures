/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheafCohomology
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf

/-! Shifted morphisms and Ext for etale free sheaves. -/

@[expose] public section

universe u w

open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

open Scheme Etale

section GenericShiftedHom

universe w' v u'

variable {C : Type u'} [Category.{v} C] [Abelian C]
  [HasDerivedCategory.{w'} C] [HasExt.{w} C]

/-- Shifted maps between degree-zero objects identify additively with Ext. -/
noncomputable def Etale.shiftedHomAddEquivExt (A N : C) (n : ℕ) :
    ((DerivedCategory.Plus.singleFunctor C 0).obj A ⟶
      ((DerivedCategory.Plus.singleFunctor C 0).obj N)⟦(n : ℤ)⟧) ≃+
      Abelian.Ext.{w} A N n :=
  (AddEquiv.mk' ((ObjectProperty.fullyFaithfulι _).homEquiv.trans
      (Iso.homCongr (Iso.refl _) ((DerivedCategory.Plus.ι.commShiftIso (n : ℤ)).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj N))))
    (fun a b ↦ by
      simp only [Equiv.trans_apply, Iso.homCongr_apply, Iso.refl_inv]
      erw [Functor.FullyFaithful.homEquiv_apply, Functor.FullyFaithful.homEquiv_apply,
        Functor.FullyFaithful.homEquiv_apply, Functor.map_add, Preadditive.add_comp]
      exact Preadditive.comp_add _ _ _ _ _ _) :
      _ ≃+ ShiftedHom ((DerivedCategory.singleFunctor _ 0).obj A)
        ((DerivedCategory.singleFunctor _ 0).obj N) (n : ℤ)).trans
    (Abelian.Ext.homAddEquiv (X := A) (Y := N) (n := n)).symm

private theorem shiftedHomExt_naturality (A : C) {N N' : C} (g : N ⟶ N') (n : ℕ)
    (f : (DerivedCategory.Plus.singleFunctor C 0).obj A ⟶
      ((DerivedCategory.Plus.singleFunctor C 0).obj N)⟦(n : ℤ)⟧) :
    Etale.shiftedHomAddEquivExt A N' n
        (f ≫ (shiftFunctor (DerivedCategory.Plus C) (n : ℤ)).map
          ((DerivedCategory.Plus.singleFunctor C 0).map g)) =
      (Etale.shiftedHomAddEquivExt A N n f).comp (Abelian.Ext.mk₀ g) (add_zero n) := by
  have key {N₀ : C} (y : ShiftedHom
      ((DerivedCategory.singleFunctor _ 0).obj A) ((DerivedCategory.singleFunctor _ 0).obj N₀)
        (n : ℤ)) : (Abelian.Ext.homAddEquiv.{w', w}.symm y).hom = y :=
    (Abelian.Ext.homAddEquiv.{w', w} (X := A) (Y := N₀) (n := n)).apply_symm_apply y
  apply Abelian.Ext.homAddEquiv.injective
  rw [Abelian.Ext.homAddEquiv_apply, Abelian.Ext.homAddEquiv_apply, Abelian.Ext.comp_hom,
    Abelian.Ext.mk₀_hom, ShiftedHom.comp_mk₀]
  simp only [Etale.shiftedHomAddEquivExt, AddEquiv.trans_apply, key]
  change 𝟙 _ ≫ DerivedCategory.Plus.ι.map (f ≫ _) ≫ _ =
    (𝟙 _ ≫ DerivedCategory.Plus.ι.map f ≫ _) ≫ _
  rw [Category.id_comp, Category.id_comp, Functor.map_comp, Category.assoc, Category.assoc]
  congr 1
  exact (DerivedCategory.Plus.ι.commShiftIso (n : ℤ)).hom.naturality
    ((DerivedCategory.Plus.singleFunctor _ 0).map g)

end GenericShiftedHom

section ShiftedHom

variable {Z : Scheme.{u}}

end ShiftedHom

end AlgebraicGeometry
