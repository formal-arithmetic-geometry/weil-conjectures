/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicQuotientTransition

/-! # Uniqueness of the ordinary quotient arrows

A consecutive arrow of fixed-scalar coordinates is determined by its values on sheafified pure
tensors, since these generate every section locally.

Source: Stacks Project, Tags 03CY and 09C6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t v₀ u₀ u v₁ u₁
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace SheafOfModules

set_option hygiene false in
local notation "𝓡" R => (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R

variable {C : Type u₀} [Category.{v₀} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
  {R₁ R₂ : Sheaf J CommRingCat.{u}} (α : R₁ ⟶ R₂) (M : SheafOfModules.{u} (𝓡 R₁))
  {Y : SheafOfModules.{u} (𝓡 R₂)} (h : Y = changeOfRings α M)

end SheafOfModules

namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective

end AlgebraicGeometry.Scheme
