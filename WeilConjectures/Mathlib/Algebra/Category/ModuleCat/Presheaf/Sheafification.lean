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
sheafification of a presheaf of modules sends zero to zero.
-/

@[expose] public section

universe v v₁ u₁ u

open CategoryTheory

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{u}} {R : Sheaf J RingCat.{u}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}] [HasWeakSheafify J AddCommGrpCat.{v}]

@[simp]
lemma sheafificationHomEquiv_zero {P : PresheafOfModules.{v} R₀} {F : SheafOfModules.{v} R} :
    sheafificationHomEquiv α (0 : (sheafification α).obj P ⟶ F) = 0 := by
  apply (toPresheaf R₀).map_injective
  rw [toPresheaf_map_sheafificationHomEquiv_def]
  change _ ≫ (toPresheaf R.obj).map 0 = _
  simp

@[simp]
lemma sheafificationHomEquiv_symm_zero {P : PresheafOfModules.{v} R₀}
    {F : SheafOfModules.{v} R} :
    (sheafificationHomEquiv α).symm (0 : P ⟶ _) = (0 : (sheafification α).obj P ⟶ F) := by
  rw [Equiv.symm_apply_eq, sheafificationHomEquiv_zero]

end PresheafOfModules
