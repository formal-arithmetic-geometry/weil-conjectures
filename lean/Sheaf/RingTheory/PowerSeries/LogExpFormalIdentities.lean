/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N6
-/
module

public import Mathlib.RingTheory.PowerSeries.Log

/-!
# Formal compositional inverse identities for logarithm and exponential

Source: Weil conjectures blueprint, main-20261015, sec-purity-real-sheaves,
sk-d-real-log, lem-wf-deep-principal-unit-log.proof.md, paragraph 3, the formal inverse
identities (blueprint: lem-wf-log-exp-formal-identities).
-/

@[expose] public section

universe u

namespace PowerSeries

/-- The formal series `log R = ∑_{n ≥ 1} (-1)^(n+1) X^n/n` and
`exp R - 1 = ∑_{n ≥ 1} X^n/n!` are compositional inverses over every commutative
rational algebra, without any topology or convergence assumptions.

Source: blueprint main-20261015, sec-purity-real-sheaves/sk-d-real-log,
lem-wf-deep-principal-unit-log.proof.md, paragraph 3
(blueprint: lem-wf-log-exp-formal-identities).

Proof plan:
1. Put `E = exp R`, `A = E - 1`, `L = log R`, and let `B` have coefficient
   `(-1)^n` in degree `n`. The defining coefficients give `DE = DA = E`, `DL = B`,
   `(1 + X) * B = 1`, and constant coefficients `A(0) = L(0) = 0`, `E(0) = 1`.
   These are coefficient computations in def-weil-formal-power-series.
2. For `H = L ∘ A`, lem-wf-formal-substitution-chain-rule gives `DH = (B ∘ A) * E`.
   Applying lem-wf-formal-substitution-hom to `(1 + X) * B = 1` gives
   `(1 + A) * (B ∘ A) = 1`, hence `DH = 1`.
3. Since `H(0) = 0`, comparison of coefficients of `DH = 1` yields `h₁ = 1`
   and `(n + 1) * h_{n+1} = 0` for `n ≥ 1`. Multiplying by the rational inverse
   of `n + 1` proves `H = X`.
4. For `K = E ∘ L`, the same chain rule gives `DK = K * B`, whence
   `(1 + X) * DK = K`. The substitution homomorphism preserves subtraction and
   constants, so `A ∘ L = K - 1`.
5. Now `k₀ = 1`, and comparison of coefficients gives `k₁ = 1` and
   `(n + 1) * k_{n+1} = (1 - n) * k_n` for `n ≥ 1`. Thus `k₂ = 0`, and induction
   using rational inverses gives all higher coefficients zero. Therefore `K = 1 + X`
   and `A ∘ L = X`. Every substituted series has constant coefficient zero, so all
   coefficient sums are finite. This also covers the zero ring and nilpotents. -/
theorem log_exp_sub_one_formal_identities (R : Type u) [CommRing R] [Algebra ℚ R] :
    (log R).subst (exp R - 1) = (X : PowerSeries R) ∧
      (exp R - 1).subst (log R) = (X : PowerSeries R) := by
  sorry

end PowerSeries
