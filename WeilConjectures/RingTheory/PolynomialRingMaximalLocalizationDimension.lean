/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.KrullDimension.Zero

/-!
# Dimension of a localized polynomial ring at a maximal ideal

For a field `k`, the localization of `k[X₁, …, Xₙ]` at any maximal ideal has Krull dimension `n`.

## Implementation details

The proof inducts on the number of variables using `finSuccEquiv`,
`Polynomial.isMaximal_comap_C_of_isJacobsonRing` and `Polynomial.height_eq_height_add_one`. This
avoids the explicit construction of generators and prime chains in the Stacks Project proof.

## References

* [Stacks, Tag 00OP]
-/

@[expose] public section

universe u

namespace MvPolynomial

/-- Induction on the variables, using the polynomial height step over a Jacobson ring. -/
private theorem height_maximal_eq_numVariables {k : Type u} [Field k] (n : ℕ)
    (M : Ideal (MvPolynomial (Fin n) k)) [M.IsMaximal] : M.height = n := by
  induction n with
  | zero =>
    have h := M.height_le_ringKrullDim_of_ne_top Ideal.IsPrime.ne_top'
    have hd : ringKrullDim (MvPolynomial (Fin 0) k) = 0 := by
      simp only [ringKrullDim_of_isNoetherianRing_of_finite, Nat.card_fin, Nat.cast_zero, add_zero]
      exact ringKrullDimZero_iff_ringKrullDim_eq_zero.mp inferInstance
    rw [hd] at h
    simpa using h
  | succ n ih =>
    let e := (finSuccEquiv k n).toRingEquiv
    let P := M.map e
    have : P.IsMaximal := Ideal.map_isMaximal_of_equiv e
    let p := P.comap Polynomial.C
    have : p.IsMaximal := Polynomial.isMaximal_comap_C_of_isJacobsonRing P
    have : P.LiesOver p := ⟨rfl⟩
    rw [← e.height_map M, Polynomial.height_eq_height_add_one p P, ih p]
    simp

/--
For a field `k`, the localization of `k[X₁, …, Xₙ]` at any maximal ideal has
Krull dimension `n`.
-/
theorem ringKrullDim_localizationAtMaximal {k : Type u} [Field k] (n : ℕ)
    (M : Ideal (MvPolynomial (Fin n) k)) [M.IsMaximal] :
    ringKrullDim (Localization.AtPrime M) = (n : WithBot ℕ∞) := by
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height M (Localization.AtPrime M),
    height_maximal_eq_numVariables n M]
  rfl

end MvPolynomial
