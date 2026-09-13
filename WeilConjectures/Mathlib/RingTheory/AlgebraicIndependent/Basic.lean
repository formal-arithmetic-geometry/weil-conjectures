/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Algebraic independence of the variables in a quotient of a polynomial ring

## Main results

* `MvPolynomial.algebraicIndependent_quotient_span_singleton`: if the variable `i` occurs in a
  polynomial `g`, then the images of all the other variables in `k[X] ⧸ (g)` are algebraically
  independent over `k`.
-/

@[expose] public section

namespace MvPolynomial

variable {σ k : Type*} [CommRing k] [IsDomain k]

/-- If the variable `i` occurs in a polynomial `g`, then the images of all the other variables
in `k[X] ⧸ (g)` are algebraically independent over `k`. -/
theorem algebraicIndependent_quotient_span_singleton {g : MvPolynomial σ k} {i : σ}
    (hi : i ∈ g.vars) :
    AlgebraicIndependent k fun j : {j : σ // j ≠ i} ↦
      Ideal.Quotient.mk (Ideal.span {g}) (X (j : σ)) := by
  classical
  have hg0 : g ≠ 0 := by
    rintro rfl
    simp at hi
  rw [algebraicIndependent_iff_injective_aeval]
  have key : (aeval fun j : {j : σ // j ≠ i} ↦ Ideal.Quotient.mk (Ideal.span {g}) (X (j : σ)) :
        MvPolynomial {j : σ // j ≠ i} k →ₐ[k] _) =
      (Ideal.Quotient.mkₐ k (Ideal.span {g})).comp (rename Subtype.val) :=
    algHom_ext fun j ↦ by simp
  rw [key, injective_iff_map_eq_zero]
  intro f hf
  simp only [AlgHom.coe_comp, Function.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
    Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hf
  by_contra hne
  -- `rename Subtype.val f` is divisible by `g`, so its degree in `i` is at least that of `g`
  have hfne : rename (Subtype.val : {j : σ // j ≠ i} → σ) f ≠ 0 := fun hc ↦
    hne (rename_injective _ Subtype.val_injective (by simpa using hc))
  have hvars : (rename (Subtype.val : {j : σ // j ≠ i} → σ) f).degreeOf i = 0 := by
    by_contra hc
    obtain ⟨j, -, hj⟩ := mem_vars_rename _ _ (mem_vars_iff_degreeOf_ne_zero.mpr hc)
    exact j.2 hj
  obtain ⟨c, hc⟩ := hf
  have hcne : c ≠ 0 := by
    rintro rfl
    exact hfne (by simpa using hc)
  rw [hc, degreeOf_mul_eq hg0 hcne] at hvars
  have := mem_vars_iff_degreeOf_ne_zero.mp hi
  omega

end MvPolynomial
