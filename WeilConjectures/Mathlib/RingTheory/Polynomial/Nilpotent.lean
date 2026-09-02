/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Polynomial.Nilpotent

/-!
# Nilpotency of `q(x) - q(μ)`

## Main results

- `IsNilpotent.aeval_sub_algebraMap_eval` — if `x - μ` is nilpotent in an `R`-algebra, then so is
  `q(x) - q(μ)` for every polynomial `q` over `R`.
-/

@[expose] public section

open Polynomial

/-- If `x - μ` is nilpotent, then so is `q(x) - q(μ)` for every polynomial `q`. -/
theorem IsNilpotent.aeval_sub_algebraMap_eval {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    {x : A} {μ : R} (h : IsNilpotent (x - algebraMap R A μ)) (q : R[X]) :
    IsNilpotent (aeval x q - algebraMap R A (q.eval μ)) := by
  -- `q - C (q.eval μ)` is divisible by `X - C μ`; apply `aeval x` to that factorisation.
  obtain ⟨r, hr⟩ := X_sub_C_dvd_sub_C_eval (a := μ) (p := q)
  have hx := congrArg (aeval x) hr
  simp only [map_mul, map_sub, aeval_X, aeval_C] at hx
  have hc := (Commute.all (X - C μ) r).map (aeval x)
  simp only [map_sub, aeval_X, aeval_C] at hc
  rw [hx]
  exact hc.isNilpotent_mul_right h
