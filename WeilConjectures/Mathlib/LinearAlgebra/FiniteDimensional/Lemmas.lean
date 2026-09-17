/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Additivity of the dimension along a short exact sequence

Mathlib has the rank-nullity theorem `LinearMap.finrank_range_add_finrank_ker`. This file
records its usual reformulation: the dimension is additive along a short exact sequence of
vector spaces, together with `LinearMap.bijective_of_ne_zero_of_finrank_eq_one`: a non-zero
linear map between two one-dimensional vector spaces is bijective.
-/

@[expose] public section

open Module

namespace LinearMap

variable {K V₁ V₂ V₃ : Type*} [DivisionRing K]
  [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂] [Module K V₂]
  [AddCommGroup V₃] [Module K V₃]

/-- **The dimension is additive along a short exact sequence** of vector spaces. -/
theorem finrank_add_finrank_of_exact [FiniteDimensional K V₂] (f : V₁ →ₗ[K] V₂)
    (g : V₂ →ₗ[K] V₃) (hf : Function.Injective f) (hg : Function.Surjective g)
    (h : range f = ker g) :
    finrank K V₂ = finrank K V₁ + finrank K V₃ := by
  have h₁ := g.finrank_range_add_finrank_ker
  rw [← h, ← (LinearEquiv.ofInjective f hf).finrank_eq,
    (LinearEquiv.ofTop _ (range_eq_top.2 hg)).finrank_eq] at h₁
  omega

/-- **A non-zero linear map between one-dimensional vector spaces is bijective.** -/
theorem bijective_of_ne_zero_of_finrank_eq_one (h₁ : finrank K V₁ = 1) (h₂ : finrank K V₂ = 1)
    {f : V₁ →ₗ[K] V₂} (hf : f ≠ 0) : Function.Bijective f := by
  have : FiniteDimensional K V₁ := Module.finite_of_finrank_pos (by omega)
  have : FiniteDimensional K V₂ := Module.finite_of_finrank_pos (by omega)
  have hsurj : Function.Surjective f := _root_.surjective_of_nonzero_of_finrank_eq_one h₂ hf
  exact ⟨(injective_iff_surjective_of_finrank_eq_finrank (h₁.trans h₂.symm)).2 hsurj, hsurj⟩

end LinearMap
