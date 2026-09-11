/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Multivariate polynomials are determined by their values at integer points

Over an integral domain of characteristic zero, the integer points form a box with infinite
sides, so `MvPolynomial.funext_set` applies. This is `lem:deg-numerical-unique` of the blueprint
chapter on the degree of an isogeny.
-/

@[expose] public section

namespace MvPolynomial

/-- A multivariate polynomial over an integral domain of characteristic zero is determined by its
values at integer points. -/
theorem funext_intCast {σ R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    {p q : MvPolynomial σ R}
    (h : ∀ x : σ → ℤ, eval (fun i ↦ (x i : R)) p = eval (fun i ↦ (x i : R)) q) : p = q := by
  refine funext_set (fun _ ↦ Set.range ((↑) : ℤ → R))
    (fun _ ↦ Set.infinite_range_of_injective Int.cast_injective) fun x hx ↦ ?_
  have hmem : ∀ i, x i ∈ Set.range ((↑) : ℤ → R) := fun i ↦ hx i (Set.mem_univ i)
  choose m hm using hmem
  have hx' : x = fun i ↦ ((m i : ℤ) : R) := by funext i; exact (hm i).symm
  rw [hx']
  exact h m

/-- A multivariate polynomial over an integral domain of characteristic zero vanishing at every
integer point is zero. -/
theorem eq_zero_of_eval_intCast_eq_zero {σ R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    {p : MvPolynomial σ R} (h : ∀ x : σ → ℤ, eval (fun i ↦ (x i : R)) p = 0) : p = 0 :=
  funext_intCast fun x ↦ by rw [h x, map_zero]

end MvPolynomial
