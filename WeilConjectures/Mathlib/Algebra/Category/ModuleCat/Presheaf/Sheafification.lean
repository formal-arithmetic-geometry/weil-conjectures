/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Sheafification of presheaves of modules

The bijection `PresheafOfModules.sheafificationHomEquiv` of the universal property of the
sheafification of a presheaf of modules is natural in the target sheaf.
-/

@[expose] public section

universe v v₁ u₁ u

open CategoryTheory

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{u}} {R : Sheaf J RingCat.{u}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}] [HasWeakSheafify J AddCommGrpCat.{v}]

lemma sheafificationHomEquiv_symm_comp {P : PresheafOfModules.{v} R₀}
    {F G : SheafOfModules.{v} R}
    (f : P ⟶ (restrictScalars α).obj ((SheafOfModules.forget _).obj F)) (g : F ⟶ G) :
    (sheafificationHomEquiv α).symm (f ≫ (restrictScalars α).map g.val) =
      (sheafificationHomEquiv α).symm f ≫ g := by
  obtain ⟨h, rfl⟩ := (sheafificationHomEquiv α).surjective f
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_eq]
  apply (toPresheaf R₀).map_injective
  rw [toPresheaf_map_sheafificationHomEquiv_def, Functor.map_comp,
    toPresheaf_map_sheafificationHomEquiv_def, SheafOfModules.comp_val, Category.assoc]
  rfl

end PresheafOfModules
