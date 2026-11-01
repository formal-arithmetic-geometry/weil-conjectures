/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.Sites.FiniteFreeCoefficientExtensionData
import all WeilConjectures.SixFunctors.FiniteFreeCoefficients.CoefficientMapDirectGeometry
import all WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDirectImage
import all WeilConjectures.CategoryTheory.ProperBaseChange.ExchangeMateCube
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.SixFunctors.Etale.Derived.WeilOperations

/-! # Scheme-isomorphism naturality for the closed coefficient counit mate -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Etale
open scoped CategoryTheory.Functor
namespace WeilConjectures.FiniteFreeCoefficients

private theorem inverseOnDomain_equivalence_square
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive] [F.ReflectsIsomorphisms]
    {X Y : C} {X' Y' : D} (f : X ⟶ Y) (g : X' ⟶ Y')
    (a : F.obj X ≅ X') (b : F.obj Y ≅ Y')
    (h : F.map f ≫ b.hom = a.hom ≫ g) :
    F.map (Sites.inverseOnDomain f) ≫ a.hom =
      b.hom ≫ Sites.inverseOnDomain g := by
  classical
  have hg : g = a.inv ≫ F.map f ≫ b.hom := by
    rw [h, Iso.inv_hom_id_assoc]
  have hf : F.map f = a.hom ≫ g ≫ b.inv := by
    rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  by_cases hi : IsIso f
  · have := hi
    have : IsIso g := by rw [hg]; infer_instance
    simp only [Sites.inverseOnDomain, dif_pos hi, dif_pos (inferInstance : IsIso g)]
    apply (cancel_epi (F.map f)).mp
    simp only [← F.map_comp_assoc, IsIso.hom_inv_id, F.map_id, Category.id_comp]
    rw [reassoc_of% h, IsIso.hom_inv_id, Category.comp_id]
  · have hn : ¬ IsIso g := by
      intro hi'
      have := hi'
      have : IsIso (F.map f) := by rw [hf]; infer_instance
      exact hi (isIso_of_reflects_iso f F)
    simp only [Sites.inverseOnDomain, dif_neg hi, dif_neg hn,
      F.map_zero, zero_comp, comp_zero]

local instance pull_additive (A : Type (u + 1)) [CommRing A]
    {Y X : Scheme.{u}} (g : Y ⟶ X) : (Sites.pull A g).Additive := by
  dsimp only [Sites.pull]
  infer_instance

local instance pull_equivalence (A : Type (u + 1)) [CommRing A]
    {Y X : Scheme.{u}} (g : Y ⟶ X) [IsIso g] : (Sites.pull A g).IsEquivalence := by
  dsimp only [Sites.pull]
  infer_instance

end WeilConjectures.FiniteFreeCoefficients
