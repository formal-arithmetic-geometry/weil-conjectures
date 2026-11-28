/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced

/-!
# Sectionwise criteria for sheaves of modules

* `SheafOfModules.isIso_of_bijective_app`: a morphism of sheaves of modules which is bijective
  on all sections is an isomorphism.
* `SheafOfModules.isZero_of_subsingleton`: a sheaf of modules all of whose sections are
  subsingletons is zero.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace SheafOfModules

variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u + 1}}

/-- A morphism of module sheaves which is bijective on all sections is an isomorphism. -/
theorem isIso_of_bijective_app {M N : SheafOfModules.{u + 1} R} (f : M ⟶ N)
    (hf : ∀ W : Cᵒᵖ, Function.Bijective (f.val.app W)) : IsIso f := by
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _),
    NatTrans.isIso_iff_isIso_app]
  intro W
  exact (ConcreteCategory.isIso_iff_bijective _).mpr (hf W)

/-- A module sheaf all of whose sections are subsingletons is zero. -/
theorem isZero_of_subsingleton (M : SheafOfModules.{u + 1} R)
    (h : ∀ W : Cᵒᵖ, Subsingleton (M.val.obj W)) : IsZero M := by
  rw [IsZero.iff_id_eq_zero]
  ext W x
  exact Subsingleton.elim _ _

end SheafOfModules
