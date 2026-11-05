/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedCalculusSupplement

/-! # Evaluation of restriction to an open slice

Source: Stacks Project, Tags 03DI and 03DJ. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe c v r c₁ v₁ r₁
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.SemilinearSections

-- Keep the coefficient sheaves abstract when checking the identity section maps.
-- This avoids unfolding the concrete sequence-ring construction in the kernel.

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)
attribute [local irreducible] systemRing ringPresheaf rings

end WeilConjectures.SemilinearSections
