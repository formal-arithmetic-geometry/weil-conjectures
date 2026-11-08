/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Transition maps between changes of rings

For morphisms of sheaves of commutative rings `α : R₁ ⟶ R₂`, `β : R₂ ⟶ R₃` and
`γ = α ≫ β`, and a sheaf of `R₁`-modules `M`, this file constructs the `R₂`-linear map
`M ⊗_{R₁} R₂ ⟶ M ⊗_{R₁} R₃` (with `R₃` regarded as an `R₂`-algebra through `β`) sending
`s ⊗ m` to `β s ⊗ m`.

Source: Stacks Project, Tag 03EK.
-/

@[expose] public section

universe v₀ u₀ u

open CategoryTheory
open scoped ChangeOfRings

namespace SheafOfModules

set_option hygiene false in
local notation "𝓡" R => (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R

variable {C : Type u₀} [Category.{v₀} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

variable {R₁ R₂ R₃ : Sheaf J CommRingCat.{u}} (α : R₁ ⟶ R₂) (β : R₂ ⟶ R₃) (γ : R₁ ⟶ R₃)
  (h : α ≫ β = γ) (M : SheafOfModules.{u} (𝓡 R₁))

variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]

local instance changeOfRingsTransitionRestrictedModule {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    Module (R₁.obj.obj Y)
      ((ModuleCat.restrictScalars ((𝓡 R₁).obj.map f).hom).obj (M.val.obj Y)) :=
  inferInstanceAs (Module (R₁.obj.obj Y) (M.val.obj Y))

section OfEq

variable {E₂ : SheafOfModules.{u} (𝓡 R₁) ⥤ SheafOfModules.{u} (𝓡 R₂)}
  {E₃ : SheafOfModules.{u} (𝓡 R₁) ⥤ SheafOfModules.{u} (𝓡 R₃)}
  (h₂ : ∀ M, E₂.obj M = changeOfRings α M)
  (hm₂ : ∀ {M N : SheafOfModules.{u} (𝓡 R₁)} (a : M ⟶ N),
    E₂.map a = eqToHom (h₂ M) ≫ changeOfRingsHom α M a ≫ eqToHom (h₂ N).symm)
  (h₃ : ∀ M, E₃.obj M = changeOfRings γ M)
  (hm₃ : ∀ {M N : SheafOfModules.{u} (𝓡 R₁)} (a : M ⟶ N),
    E₃.map a = eqToHom (h₃ M) ≫ changeOfRingsHom γ M a ≫ eqToHom (h₃ N).symm)

end OfEq

end SheafOfModules
