/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Basic
public import WeilConjectures.RingTheory.FormalInitialDiagram
public import WeilConjectures.RingTheory.SupportedHomogeneousDivision

/-! # Supported division of multivariate formal power series

Source: Bierstone--Milman 1997, Theorem 3.17 and Remark 3.18, printed p.238;
historical local-presentation route of ILO VIII 2.3.11--2.3.13.
(blueprint: lem-trf-supported-formal-division)

The first exponent and first-dividing-vertex supports are the existing definitions
`MonomialDiagram.IsFirstExponent` and `MonomialDiagram.quotientSupport`.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace MonomialDiagram

/-- Unique supported formal division, with the total-degree estimates.

Source: Bierstone--Milman 1997, Theorem 3.17 and Remark 3.18, printed p.238;
historical local-presentation route of ILO VIII 2.3.11--2.3.13.
(blueprint: lem-trf-supported-formal-division).

Here `hα` says that each divisor has the prescribed least nonzero exponent, in
ascending lexicographic order of `(total degree, coordinates)`. In particular it
includes nonzeroness of every divisor. `quotientSupport α i` is the translated
region Δᵢ, and the complement of `generated α` is E₀. `Function.support` is exactly
the set of exponents with nonzero coefficient. Uniqueness quantifies over all
supported decompositions, without presupposing their degree estimates.

Proof plan (the node's agent-written coefficient proof; BM remains WANTED):
1. In degree-lex order every exponent has finitely many predecessors: each
coordinate in degree at most d is at most d. Minimize degree, then the finite
lexicographic list. Translation preserves the order, including with no variables.
2. Assign an exponent to the first orthant containing it, or to the remainder.
This partitions all exponents even when initial exponents repeat; subtraction
of the vertex identifies each quotient region with its translated support.
3. Write cᵢ for the nonzero initial coefficient. Using field inverses
[def-weil-field] and finite convolution [def-weil-pbc-multivariate-power-series],
the normalized column Cμ = cᵢ⁻¹ T^β Gᵢ at μ = αᵢ + β has coefficient 1 at μ
and vanishes at all earlier exponents. Remainder columns are T^μ.
4. Define aν = fν - ∑ μ < ν, aμ [T^ν]Cμ. This is finite triangular recursion:
process total degrees and then each finite degree list. Induction gives uniqueness.
5. Define quotient coefficients as cᵢ⁻¹ a(αᵢ + β) on Δᵢ and zero elsewhere;
define remainder coefficients as aν on E₀ and zero elsewhere. Coefficient families
are actual series by [def-weil-pbc-multivariate-power-series]. Finite convolution
and the slot partition identify each coefficient of the resulting sum with
∑ μ ≤ ν, aμ [T^ν]Cμ; later slots and non-componentwise-dividing terms vanish.
6. The diagonal coefficient is 1, so recursion gives exactly fν. Coefficient
extensionality [def-weil-pbc-multivariate-power-series] gives the decomposition.
7. Encode any other supported decomposition by bμ = cᵢ [T^β]Qᵢ or [T^μ]R.
The same convolution identity forces the same recursion, hence b = a. Field
inverses [def-weil-field] and coefficient extensionality give Q' = Q and R' = R.
8. If fν vanishes below degree q, induction in the same order makes aν vanish
there. Thus R vanishes there, and Qᵢ vanishes below q - |αᵢ| when positive.
9. For no divisors every slot is a remainder slot and R = F. With no variables,
all series are scalars: the first divisor takes the only slot and later quotients
and the remainder vanish. Empty quotient regions also force zero quotients. -/
theorem exists_unique_supported_formal_division
    {L : Type u} [Field L] {n s : ℕ}
    (G : Fin s → MvPowerSeries (Fin n) L) (α : Fin s → Fin n →₀ ℕ)
    (hα : ∀ i : Fin s, IsFirstExponent (G i) (α i))
    (F : MvPowerSeries (Fin n) L) :
    ∃ (Q : Fin s → MvPowerSeries (Fin n) L) (R : MvPowerSeries (Fin n) L),
      F = (∑ i : Fin s, Q i * G i) + R ∧
      (∀ i : Fin s, Function.support (Q i) ⊆ quotientSupport α i) ∧
      Function.support R ⊆ (generated α)ᶜ ∧
      (∀ (Q' : Fin s → MvPowerSeries (Fin n) L) (R' : MvPowerSeries (Fin n) L),
        F = (∑ i : Fin s, Q' i * G i) + R' →
        (∀ i : Fin s, Function.support (Q' i) ⊆ quotientSupport α i) →
        Function.support R' ⊆ (generated α)ᶜ → Q' = Q ∧ R' = R) ∧
      (∀ q : ℕ,
        (∀ β : Fin n →₀ ℕ, β.degree < q → MvPowerSeries.coeff β F = 0) →
        (∀ β : Fin n →₀ ℕ, β.degree < q → MvPowerSeries.coeff β R = 0) ∧
        (∀ (i : Fin s) (β : Fin n →₀ ℕ),
          β.degree < q - (α i).degree → MvPowerSeries.coeff β (Q i) = 0)) ∧
      (s = 0 → R = F) := by
  sorry

end MonomialDiagram
