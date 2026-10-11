/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.MvPowerSeries.Trunc
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Universal property of power series over an adically complete ring

Source: Stacks Project, proofs of Tags 07NL, 07NN and 032A; agent-formulated lemma
(blueprint: lem-weil-pbc-power-series-universal-property-complete).
-/

universe u v

namespace MvPowerSeries

/-- The universal property used in Stacks Project, proofs of Tags 07NL, 07NN and 032A.
(blueprint: lem-weil-pbc-power-series-universal-property-complete)

Proof (agent-written, following the six steps of the DAG node):
1. Using def-weil-pbc-multivariate-power-series, form the finite sums P_m of terms of degree
less than m. Since every t_i lies in a, a monomial of degree d evaluates into a^d, so the
partial sums agree modulo a^m whenever the truncation degree is at least m.
2. By def-weil-pbc-adically-complete-ring, the compatible classes of P_m determine exactly
one element of T. Define Phi(F) to be this element. Separatedness also gives intersection
of all positive powers of a equal to zero.
3. Coefficientwise addition gives additivity. The constant unit evaluates to one. For products,
group the product of the two finite sums by exponent: terms of degree less than m give
P_m(FG), and all remaining terms belong to a^m. Separatedness gives multiplicativity.
4. The partial sums for a constant are alpha of that constant. Those for X_i are zero at
m = 1 and t_i at m >= 2, so Phi has the prescribed values (with no variables when n = 0).
5. Every series with zero coefficients in degrees less than m is a finite sum of x^E g_E
with degree E = m: for each exponent G of degree at least m choose E(G) <= G of degree m,
and assign its coefficient to g_{E(G)} at G - E(G). The coefficient product formula verifies
this decomposition.
6. Any ring map Psi with the prescribed values sends that remainder into a^m by step 5.
Thus Psi(F) agrees with P_m(F) modulo a^m for every positive m; step 2 gives Psi = Phi.
No continuity hypothesis is needed.

Here `F.truncTotal m` retains exactly the coefficients of total degree less than `m`, so
`MvPolynomial.eval₂ α t (F.truncTotal m)` is the finite sum of `α(a_E) * t^E` over
`|E| < m` in the node (the same form as lem-weil-pbc-power-series-adic-evaluation). -/
theorem exists_ringHom_of_isAdicComplete
    {Λ : Type u} {T : Type v} [CommRing Λ] [CommRing T]
    (a : Ideal T) [IsAdicComplete a T] (α : Λ →+* T)
    (n : ℕ) (t : Fin n → T) (ht : ∀ i : Fin n, t i ∈ a) :
    ∃ Φ : MvPowerSeries (Fin n) Λ →+* T,
      (∀ r : Λ, Φ (C r) = α r) ∧
      (∀ i : Fin n, Φ (X i) = t i) ∧
      (∀ (F : MvPowerSeries (Fin n) Λ) (y : T),
        (∀ m : ℕ, 1 ≤ m →
          Ideal.Quotient.mk (a ^ m) y =
            Ideal.Quotient.mk (a ^ m) (MvPolynomial.eval₂ α t (F.truncTotal m))) ↔
        y = Φ F) ∧
      (∀ Ψ : MvPowerSeries (Fin n) Λ →+* T,
        (∀ r : Λ, Ψ (C r) = α r) →
        (∀ i : Fin n, Ψ (X i) = t i) → Ψ = Φ) := by
  sorry

end MvPowerSeries
