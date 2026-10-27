/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M6
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.MvPolynomial.Ideal
import WeilConjectures.RingTheory.PowerSeriesCombinedIdealCoefficients

/-! # Coefficients of the combined ideal in a polynomial ring

Source: the monomial calculation in the proof of
lem-trf-smooth-rational-point-completion, Step 6.
(blueprint: lem-trf-polynomial-combined-ideal-coefficients)
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace MvPolynomial

private theorem monomial_mem_combined_pow
    {R : Type u} [CommRing R] (I : Ideal R) (d n : ℕ)
    (E : Fin d →₀ ℕ) (a : R) (ha : a ∈ I ^ (n - E.degree)) :
    monomial E a ∈ (I.map (C (σ := Fin d)) ⊔ idealOfVars (Fin d) R) ^ n := by
  classical
  nontriviality R
  let Q := I.map (C (σ := Fin d)) ⊔ idealOfVars (Fin d) R
  have hvar : monomial E (1 : R) ∈ Q ^ E.degree := by
    apply Ideal.pow_right_mono le_sup_right E.degree
    exact (monomial_mem_pow_idealOfVars_iff _ _ one_ne_zero).mpr le_rfl
  have hbase : C (σ := Fin d) a ∈ Q ^ (n - E.degree) := by
    apply Ideal.pow_right_mono le_sup_left (n - E.degree)
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ ha
  have hprod := Ideal.mul_mem_mul hbase hvar
  rw [← pow_add] at hprod
  apply Ideal.pow_le_pow_right (show n ≤ n - E.degree + E.degree by omega)
  simpa only [C_mul_monomial, mul_one] using hprod

/-- A polynomial belongs to `(I,X)^n` precisely when its coefficient of exponent `E`
belongs to `I^(n-degree E)`.

Source: Stacks Project, Tag 054L followed by the explicit monomial calculation in
Step 6 of lem-trf-smooth-rational-point-completion.
(blueprint: lem-trf-polynomial-combined-ideal-coefficients)

Proof: The coefficient criterion for the combined power-series ideal implies the
forward inclusion after embedding polynomials as series. For the reverse inclusion,
write the polynomial as its finite sum of monomials. The monomial of exponent E is
in the degree(E)-th power of the variables ideal, and its coefficient is in the
(n-degree(E))-th power of I. Multiply these memberships and use decreasingness of
ideal powers. Exponents of degree at least n impose no condition, and n=0 gives
the whole ring. -/
theorem mem_combined_ideal_pow_iff
    (R : Type u) [CommRing R] (I : Ideal R) (d n : ℕ)
    (p : MvPolynomial (Fin d) R) :
    p ∈ (I.map (C (σ := Fin d)) ⊔ idealOfVars (Fin d) R) ^ n ↔
      ∀ E : Fin d →₀ ℕ, p.coeff E ∈ I ^ (n - E.degree) := by
  classical
  constructor
  · intro hp E
    by_cases hE : E.degree < n
    · let f : MvPolynomial (Fin d) R →+* MvPowerSeries (Fin d) R := coeToMvPowerSeries.ringHom
      have hmap : (I.map (C (σ := Fin d)) ⊔ idealOfVars (Fin d) R).map f ≤
          I.map (algebraMap R (MvPowerSeries (Fin d) R)) ⊔
            Ideal.span (Set.range MvPowerSeries.X) := by
        have hC : f.comp (C (σ := Fin d)) = MvPowerSeries.C := by
          apply RingHom.ext
          intro a
          exact coe_C a
        have hX : (f ∘ (X (σ := Fin d))) = MvPowerSeries.X := by
          funext i
          exact coe_X i
        rw [Ideal.map_sup, Ideal.map_map, hC]
        apply sup_le
        · exact le_sup_left
        · rw [idealOfVars, Ideal.map_span, ← Set.range_comp, hX]
          exact le_sup_right
      have hs := Ideal.mem_map_of_mem f hp
      rw [Ideal.map_pow] at hs
      have hs := Ideal.pow_right_mono hmap n hs
      exact (power_series_mem_combined_ideal_pow_iff R I d n (f p)).mp hs E hE
    · simp [Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hE)]
  · intro hp
    rw [p.as_sum]
    apply Submodule.sum_mem
    intro E hE
    exact monomial_mem_combined_pow I d n E (p.coeff E) (hp E)

end MvPolynomial
