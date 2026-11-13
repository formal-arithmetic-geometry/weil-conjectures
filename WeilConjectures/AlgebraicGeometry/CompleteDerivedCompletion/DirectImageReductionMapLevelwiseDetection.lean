/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompleteDerivedCompletion.CompleteDerivedCompletion

/-! # Levelwise detection of isomorphisms of derived reduction towers
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale.CompleteDerivedCompletion

attribute [local instance] AdicCompletion.ringMonoidalObject
  AdicCompletion.ringCommutative AdicCompletion.modulesDerived

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable {T : Scheme.{u}}

/-- Isomorphisms of derived reduction towers are detected at every finite level. -/
theorem directImage_pushReductionMap_levelwiseDetection
    {M N : CompleteDerivedCompletion.DTow l E T} (a : M ⟶ N)
    (ha : ∀ n : ℕ, IsIso ((CompleteDerivedCompletion.dev l E T n).map a)) :
    IsIso a := by
  exact ((completeDerivedCompletion l E T T (𝟙 T)).2.2.1 a).mpr ha

end AlgebraicGeometry.ProEtale.CompleteDerivedCompletion
