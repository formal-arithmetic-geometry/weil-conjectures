/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.MvPowerSeries.Trunc
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Homogeneous approximations and preimages for adic evaluation

Source: Stacks Project, Divided Power Algebra, Tag 09PZ (`lemma-ci-well-defined`),
third paragraph of the proof, omitted surjectivity details
(blueprint: lem-trf-adic-evaluation-homogeneous-preimages).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace MvPowerSeries

/-- Adic evaluation admits homogeneous corrections with compatible total-degree truncations.
Source: Stacks Project, Divided Power Algebra, Tag 09PZ (`lemma-ci-well-defined`),
third paragraph of the proof, omitted surjectivity details
(blueprint: lem-trf-adic-evaluation-homogeneous-preimages).

Here `J` is written as `Ideal.span (Set.range b)`, `S_N` as the finite sum of `H k`
for `k < N`, and the finite substitution sum as `MvPolynomial.eval₂ f b (F.truncTotal N)`.

Proof:
1. The variables lie in `I`, so `J ≤ I`. For any polynomial, apply the reduction formula
   above its degree and then at every smaller positive precision. Separatedness from
   def-weil-pbc-adically-complete-ring makes its evaluation exactly finite substitution.
2. By lem-trf-finite-support-monomial-ideal-power, an element of `J ^ N` is a finite sum
   of multiples of degree-`N` monomials in `b`. Lift each coefficient modulo `J` along `f`.
   The resulting degree-`N` homogeneous polynomial has evaluation congruent to that element
   modulo `J ^ (N + 1)`. For `N = 0` this is the lift of its residue modulo `J`.
3. Starting with the zero partial sum, recursively apply step 2 to the residual of `z`.
   Add the homogeneous correction. Additivity of `E` gives the residual in `J ^ (N + 1)`;
   induction gives all residual and increment identities and the asserted finite sums.
4. Using def-weil-pbc-multivariate-power-series, assemble `S` coefficientwise: its coefficient
   at an exponent of total degree `N` is that of `H N`. Finitely many exponent vectors
   have degree below each bound. Homogeneity proves that its truncation is the partial sum,
   including at zero.
5. The reduction formula for `S`, step 4, and exact polynomial evaluation give the tail
   in `I ^ N`. The residual lies in `J ^ N ≤ I ^ N`; subtracting and using separatedness
   gives `E S = z`. Since `z` is arbitrary, `E` is surjective.
6. With no variables, `J = 0` and the quotient surjection lifts `z` to a constant `H 0`.
   Take all positive-degree corrections zero and `S` that constant. Zero corrections also
   cover `J = 0`, nilpotent ideals, and the zero ring. -/
theorem exists_homogeneous_preimages_of_adic_evaluation
    {C : Type u} {R : Type v} [CommRing C] [CommRing R]
    (I : Ideal R) [IsAdicComplete I R] (f : C →+* R) (s : ℕ)
    (b : Fin s → R) (hb : ∀ j : Fin s, b j ∈ I)
    (hf : Function.Surjective ((Ideal.Quotient.mk (Ideal.span (Set.range b))).comp f))
    (E : MvPowerSeries (Fin s) C →+* R)
    (hE : ∀ (F : MvPowerSeries (Fin s) C) (N : ℕ), 1 ≤ N →
      E F - MvPolynomial.eval₂ f b (F.truncTotal N) ∈ I ^ N) :
    (∀ z : R, ∃ (H : ℕ → MvPolynomial (Fin s) C) (S : MvPowerSeries (Fin s) C),
      (∀ N : ℕ, (H N).IsHomogeneous N) ∧
      (∑ k ∈ Finset.range 0, H k) = 0 ∧
      (∀ N : ℕ,
        z - E (MvPolynomial.toMvPowerSeries (∑ k ∈ Finset.range N, H k)) ∈
          (Ideal.span (Set.range b)) ^ N) ∧
      (∀ N : ℕ,
        (∑ k ∈ Finset.range (N + 1), H k) - (∑ k ∈ Finset.range N, H k) = H N) ∧
      (∀ N : ℕ, S.truncTotal N = ∑ k ∈ Finset.range N, H k) ∧
      (∀ N : ℕ, 1 ≤ N →
        E S - E (MvPolynomial.toMvPowerSeries (∑ k ∈ Finset.range N, H k)) ∈ I ^ N) ∧
      E S = z ∧
      (s = 0 → ∀ N : ℕ, 0 < N → H N = 0)) ∧
    Function.Surjective E := by
  sorry

end MvPowerSeries
