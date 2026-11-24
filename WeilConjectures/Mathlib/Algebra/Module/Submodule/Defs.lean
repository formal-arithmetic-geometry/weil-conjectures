/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Module.Submodule.Defs

/-!
# Subsets underlying submodules

## Main statements

- `Submodule.exists_coe_eq_iff`: a subset of a module is the carrier of a submodule if and only
  if it contains `0` and is closed under addition and scalar multiplication.
-/

@[expose] public section

namespace Submodule

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- A subset `s` of a module is the carrier of a `Submodule` if and only if it contains `0` and
is closed under addition and scalar multiplication. -/
theorem exists_coe_eq_iff (s : Set M) :
    (∃ V : Submodule R M, (V : Set M) = s) ↔
      (0 : M) ∈ s ∧ (∀ a ∈ s, ∀ b ∈ s, a + b ∈ s) ∧ ∀ (c : R), ∀ a ∈ s, c • a ∈ s := by
  constructor
  · rintro ⟨V, rfl⟩
    exact ⟨V.zero_mem, fun _ ha _ hb ↦ V.add_mem ha hb, fun c _ ha ↦ V.smul_mem c ha⟩
  · rintro ⟨h0, hadd, hsmul⟩
    exact ⟨{ carrier := s
             add_mem' := fun ha hb ↦ hadd _ ha _ hb
             zero_mem' := h0
             smul_mem' := fun c _ ha ↦ hsmul c _ ha }, rfl⟩

end Submodule
