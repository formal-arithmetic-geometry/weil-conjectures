/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import WeilConjectures.RingTheory.AssociatedGradedRing
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Finite-support monomial expansions in powers of a combined ideal

Source: Illusie–Laszlo–Orgogozo, Travaux de Gabber, Exposé VI, §1.6(i)–(ii),
printed p. 70, provides the formal-monoid context. The auxiliary finite coefficient
argument is supplied by the DAG, not asserted as a theorem of ILO
(blueprint: lem-trf-finite-support-monomial-ideal-power).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace Ideal

open scoped BigOperators

open Classical in
/-- Finite generator expansions and their substitution into a monomial ideal power.

Source: the auxiliary coefficient argument in the DAG, motivated by ILO, Exposé VI,
§1.6(i)–(ii), printed p. 70
(blueprint: lem-trf-finite-support-monomial-ideal-power).

Proof plan:
1. Induct on `k`, using `J ^ 0 = ⊤` and `J ^ (k + 1) = J ^ k * J`, the
   ideal-power convention of `def-weil-pbc-associated-graded-ring`. In degree zero
   write `a = a * 1`. At the successor step express an element of the ideal product
   as a finite sum of `x * y`. Expand `x` by induction and `y` in the generators
   `t`, and distribute. Conversely each generator product belongs to the power,
   as do its scalar multiples and their finite sums. With no generators, a
   positive-length word is impossible, so only the empty sum zero remains.
2. Fix `p` in `S`, an arbitrary nonzero decomposition `d` of length `l p`, and
   an arbitrary coefficient expansion of length `n - l p`. Iterate `hzadd` and
   `hz0` to identify `z p` with the product of the `z (d s)`. Apply the ring
   homomorphism laws of `C` and distribute to obtain the displayed finite sum.
3. Each `C (t j)` is in `b` because `t j` is in `J`; each `z (d s)` is in `b`
   because `d s` is nonzero. There are `(n - l p) + l p = n` such factors.
   Their product, and its multiple by `C (c α)`, belong to `b ^ n`. Sum over
   the coefficient expansion, then over `S`. Empty sums are zero, so empty
   `S`, an empty generator list, and length-zero decompositions are included.
-/
theorem finite_support_monomial_ideal_power
    (A : Type u) [CommRing A] (B : Type v) [CommRing B]
    (C : A →+* B) (P : Type w) [AddCommMonoid P]
    (z : P → B) (hz0 : z 0 = 1) (hzadd : ∀ p q : P, z (p + q) = z p * z q)
    (h : ℕ) (t : Fin h → A) (J : Ideal A) (hJ : J = Ideal.span (Set.range t))
    (b : Ideal B)
    (hb : b = Ideal.span (C '' (J : Set A) ∪ z '' {q : P | q ≠ 0})) :
    (∀ (k : ℕ) (a : A), a ∈ J ^ k ↔
      ∃ (m : ℕ) (c : Fin m → A) (j : Fin m → Fin k → Fin h),
        a = ∑ α : Fin m, c α * ∏ r : Fin k, t (j α r)) ∧
    (∀ (S : Finset P) (n : ℕ), 1 ≤ n →
      ∀ (l : P → ℕ) (a : P → A),
        (∀ p ∈ S, l p < n) →
        (∀ p ∈ S, ∃ d : Fin (l p) → P,
          (∀ s : Fin (l p), d s ≠ 0) ∧ (∑ s : Fin (l p), d s) = p) →
        (∀ p ∈ S, a p ∈ J ^ (n - l p)) →
        (∑ p ∈ S, C (a p) * z p) ∈ b ^ n ∧
        ∀ p ∈ S, C (a p) * z p ∈ b ^ n ∧
          ∀ d : Fin (l p) → P,
            (∀ s : Fin (l p), d s ≠ 0) → (∑ s : Fin (l p), d s) = p →
            ∀ (m : ℕ) (c : Fin m → A) (j : Fin m → Fin (n - l p) → Fin h),
              a p = (∑ α : Fin m, c α * ∏ r : Fin (n - l p), t (j α r)) →
              C (a p) * z p =
                (∑ α : Fin m, C (c α) * (∏ r : Fin (n - l p), C (t (j α r))) *
                  (∏ s : Fin (l p), z (d s))) ∧
              (n - l p) + l p = n ∧
              (∀ (α : Fin m) (r : Fin (n - l p)), C (t (j α r)) ∈ b) ∧
              (∀ s : Fin (l p), z (d s) ∈ b) ∧
              (∀ α : Fin m,
                C (c α) * (∏ r : Fin (n - l p), C (t (j α r))) *
                  (∏ s : Fin (l p), z (d s)) ∈ b ^ n)) := by
  sorry

end Ideal
