/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu, Claude
-/
module

public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsTransition

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# The transition between changes of rings and the tensor units

For `γ = α ≫ β`, the transition `M ⊗_{R₁} R₂ ⟶ M ⊗_{R₁} R₃` sends `1 ⊗ m` to `1 ⊗ m`. Hence,
for scalar-extension adjunctions whose units are `m ↦ 1 ⊗ m`, the unit along `α` followed by
the transition is the unit along `γ`, up to the identification of the composite restriction.

Source: Stacks Project, Tag 03EK.
-/

@[expose] public section

universe v₀ u₀ u

open CategoryTheory
open scoped ChangeOfRings

namespace SheafOfModules

set_option hygiene false in
local notation "𝓡" R => (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R

set_option hygiene false in
local notation "𝓕" f => (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map f

variable {C : Type u₀} [Category.{v₀} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]

variable {R₁ R₂ R₃ : Sheaf J CommRingCat.{u}} (α : R₁ ⟶ R₂) (β : R₂ ⟶ R₃) (γ : R₁ ⟶ R₃)
  (h : α ≫ β = γ)
  {E₂ : SheafOfModules.{u} (𝓡 R₁) ⥤ SheafOfModules.{u} (𝓡 R₂)}
  {E₃ : SheafOfModules.{u} (𝓡 R₁) ⥤ SheafOfModules.{u} (𝓡 R₃)}
  (h₂ : ∀ M, E₂.obj M = changeOfRings α M)
  (hm₂ : ∀ {M N : SheafOfModules.{u} (𝓡 R₁)} (a : M ⟶ N),
    E₂.map a = eqToHom (h₂ M) ≫ changeOfRingsHom α M a ≫ eqToHom (h₂ N).symm)
  (h₃ : ∀ M, E₃.obj M = changeOfRings γ M)
  (hm₃ : ∀ {M N : SheafOfModules.{u} (𝓡 R₁)} (a : M ⟶ N),
    E₃.map a = eqToHom (h₃ M) ≫ changeOfRingsHom γ M a ≫ eqToHom (h₃ N).symm)

end SheafOfModules
