/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Mathlib.Algebra.Group.ForwardDiff
public import WeilConjectures.Mathlib.Algebra.MvPolynomial.Funext
public import WeilConjectures.Mathlib.Algebra.MvPolynomial.Monad

/-!
# Numerical polynomials in several variables

A function `P : ℤ ^ r → ℤ` is a *numerical polynomial of total degree at most `d`* if it is the
restriction to the integer points of a polynomial in `ℚ[T_1, …, T_r]` of total degree at most `d`.
This file introduces the predicate `IsNumericalPolynomial` and develops the difference calculus
for it.

## Main results

* `IsNumericalPolynomial`: the predicate itself (`def:deg-numerical`).
* `IsNumericalPolynomial.existsUnique`: the representing polynomial is unique, so that the total
  degree of a numerical polynomial is well defined (`lem:deg-numerical-unique`).
* `IsNumericalPolynomial.fwdDiff`: a difference operator `Δ_[v]` lowers the degree by one
  (`lem:deg-difference-lowers-degree`), with the consequences
  `IsNumericalPolynomial.fwdDiffComp_eq_zero` and
  `IsNumericalPolynomial.exists_fwdDiffComp_eq_const`.

The alternating sum expansion of a composite of difference operators
(`lem:deg-difference-explicit`) is `fwdDiffComp_eq_sum_powerset` in
`WeilConjectures/Mathlib/Algebra/Group/ForwardDiff.lean`.

## References

The blueprint chapter on the degree of an isogeny, section `sec:deg-numerical`.
-/

@[expose] public section

open Finset fwdDiff MvPolynomial

variable {r : ℕ}

/-- A function `P : ℤ ^ r → ℤ` is a *numerical polynomial of total degree at most `d`* if it is the
restriction to the integer points of a polynomial with rational coefficients of total degree at
most `d`. This is `def:deg-numerical` of the blueprint. -/
def IsNumericalPolynomial (d : ℕ) (P : (Fin r → ℤ) → ℤ) : Prop :=
  ∃ p : MvPolynomial (Fin r) ℚ, p.totalDegree ≤ d ∧
    ∀ m : Fin r → ℤ, (P m : ℚ) = eval (fun i ↦ (m i : ℚ)) p

namespace IsNumericalPolynomial

variable {d e : ℕ} {P : (Fin r → ℤ) → ℤ}

lemma mono (h : IsNumericalPolynomial d P) (hde : d ≤ e) : IsNumericalPolynomial e P := by
  obtain ⟨p, hp, hP⟩ := h
  exact ⟨p, hp.trans hde, hP⟩

/-- **The representing polynomial of a numerical polynomial is unique.**
This is `lem:deg-numerical-unique` of the blueprint. -/
theorem existsUnique (h : IsNumericalPolynomial d P) :
    ∃! p : MvPolynomial (Fin r) ℚ, p.totalDegree ≤ d ∧
      ∀ m : Fin r → ℤ, (P m : ℚ) = eval (fun i ↦ (m i : ℚ)) p := by
  obtain ⟨p, hp, hP⟩ := h
  refine ⟨p, ⟨hp, hP⟩, fun q hq ↦ MvPolynomial.funext_intCast fun m ↦ ?_⟩
  rw [← hq.2 m, hP m]

/-- A numerical polynomial of total degree at most `0` is constant. -/
theorem exists_eq_const (h : IsNumericalPolynomial 0 P) : ∃ c : ℤ, P = Function.const _ c := by
  obtain ⟨p, hp, hP⟩ := h
  refine ⟨P 0, funext fun m ↦ ?_⟩
  have hC : p = C (coeff 0 p) := totalDegree_eq_zero_iff_eq_C.mp (Nat.le_zero.mp hp)
  have hcast : (P m : ℚ) = (P 0 : ℚ) := by rw [hP m, hP 0, hC]; simp
  exact_mod_cast hcast

end IsNumericalPolynomial

/-- A constant function is a numerical polynomial of total degree at most `0`. -/
lemma isNumericalPolynomial_const (c : ℤ) :
    IsNumericalPolynomial (r := r) 0 (Function.const _ c) :=
  ⟨C (c : ℚ), (totalDegree_C _).le, fun _ ↦ by simp⟩

/-- Being a numerical polynomial of total degree at most `0` means being constant. -/
lemma isNumericalPolynomial_zero_iff {P : (Fin r → ℤ) → ℤ} :
    IsNumericalPolynomial 0 P ↔ ∃ c : ℤ, P = Function.const _ c :=
  ⟨IsNumericalPolynomial.exists_eq_const,
    fun ⟨c, hc⟩ ↦ hc ▸ isNumericalPolynomial_const c⟩

namespace IsNumericalPolynomial

variable {d e : ℕ} {P : (Fin r → ℤ) → ℤ}

/-- **Difference operators lower the degree.** This is `lem:deg-difference-lowers-degree` of the
blueprint. -/
theorem fwdDiff (h : IsNumericalPolynomial (d + 1) P) (v : Fin r → ℤ) :
    IsNumericalPolynomial d (Δ_[v] P) := by
  obtain ⟨p, hp, hP⟩ := h
  refine ⟨bind₁ (fun i ↦ X i + C ((v i : ℚ))) p - p,
    totalDegree_bind₁_X_add_C_sub_le _ _ _ hp, fun m ↦ ?_⟩
  have hΔ : (Δ_[v] P) m = P (m + v) - P m := rfl
  have harg : (fun i ↦ (((m + v) i : ℤ) : ℚ)) =
      fun i ↦ eval (fun i ↦ ((m i : ℤ) : ℚ)) (X i + C ((v i : ℚ))) := by
    funext i
    simp
  rw [hΔ, Int.cast_sub, hP (m + v), hP m, map_sub, eval_bind₁, ← harg]

/-- A difference operator kills a numerical polynomial of total degree at most `0`. -/
theorem fwdDiff_eq_zero (h : IsNumericalPolynomial 0 P) (v : Fin r → ℤ) : Δ_[v] P = 0 := by
  obtain ⟨c, rfl⟩ := h.exists_eq_const
  funext m
  simp [_root_.fwdDiff]

/-- Applying `e` difference operators to a numerical polynomial of total degree at most `d + e`
gives a numerical polynomial of total degree at most `d`. -/
theorem fwdDiffComp (h : IsNumericalPolynomial (d + e) P) (v : Fin e → (Fin r → ℤ)) :
    IsNumericalPolynomial d (_root_.fwdDiffComp v P) := by
  induction e generalizing P with
  | zero => simpa using h
  | succ e ih =>
    rw [fwdDiffComp_succ']
    refine ih ?_ _
    rw [show d + (e + 1) = (d + e) + 1 from by omega] at h
    exact h.fwdDiff (v 0)

/-- A composite of `d + 1` difference operators kills a numerical polynomial of total degree at
most `d`. -/
theorem fwdDiffComp_eq_zero (h : IsNumericalPolynomial d P) (v : Fin (d + 1) → (Fin r → ℤ)) :
    _root_.fwdDiffComp v P = 0 := by
  have h' : IsNumericalPolynomial (0 + d) P := by rwa [Nat.zero_add]
  rw [fwdDiffComp_succ]
  exact (h'.fwdDiffComp _).fwdDiff_eq_zero (v 0)

/-- A composite of `d` difference operators turns a numerical polynomial of total degree at most
`d` into a constant function. -/
theorem exists_fwdDiffComp_eq_const (h : IsNumericalPolynomial d P) (v : Fin d → (Fin r → ℤ)) :
    ∃ c : ℤ, _root_.fwdDiffComp v P = Function.const _ c := by
  have h' : IsNumericalPolynomial (0 + d) P := by rwa [Nat.zero_add]
  exact (h'.fwdDiffComp v).exists_eq_const

end IsNumericalPolynomial
