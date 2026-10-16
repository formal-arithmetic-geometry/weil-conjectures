/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheafCohomology

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

/-- Shifted morphisms `A[0] ⟶ N[0]⟦n⟧` in the bounded below derived category are
`Extⁿ(A, N)`, additively: `D⁺` is a full subcategory of the derived category, stable under
shifts. -/
noncomputable def Etale.shiftedHomFunctorObjAddEquivExt
    (A N : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (n : ℕ) :
    (Etale.shiftedHomFunctor Λ A n).obj N ≃+ Abelian.Ext.{u + 1} A N n :=
  Etale.shiftedHomAddEquivExt A N n

lemma Etale.shiftedHomFunctorObjAddEquivExt_naturality
    (A : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    {N N' : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (g : N ⟶ N') (n : ℕ)
    (f : (Etale.shiftedHomFunctor Λ A n).obj N) :
    Etale.shiftedHomFunctorObjAddEquivExt Λ A N' n ((Etale.shiftedHomFunctor Λ A n).map g f) =
      (Etale.shiftedHomFunctorObjAddEquivExt Λ A N n f).comp (Abelian.Ext.mk₀ g)
        (add_zero n) := by
  exact shiftedHomExt_naturality A g n f

end ShiftedHom

end AlgebraicGeometry
