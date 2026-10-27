/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q12
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.Rat.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs

import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Prime-chain bounds from quotient colength polynomials

Source: Stacks Project, Algebra, Tag 00KQ, `proposition-dimension`, last prime-chain
paragraph, in the conditional shifted-colength form of the DAG node
(blueprint: lem-trf-prime-chain-bound-from-colength-polynomials).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace IsLocalRing

/-- The function `H_I(n)` in the node: length over `A_I = R / I` of the quotient by
`m_I ^ n`, where `m_I` is the image of the maximal ideal of `R`. This is defined also
at `n = 0` and `I = top`, although the statement only uses positive exponents and proper
ideals. Source: Stacks Project, Algebra, Tag 00KQ, `proposition-dimension`
(blueprint: lem-trf-prime-chain-bound-from-colength-polynomials). -/
noncomputable def quotientPowerColength {R : Type u} [CommRing R] [IsLocalRing R]
    (I : Ideal R) (n : ℕ) : ℕ∞ :=
  Module.length (R ⧸ I)
    ((R ⧸ I) ⧸ ((maximalIdeal R).map (Ideal.Quotient.mk I)) ^ n)

/-- Conditional polynomial degree and prime-chain bounds for all proper quotients.
Only values of `Q` on proper ideals are constrained or used in the conclusions; its value
at `top` is immaterial. The finite-length assumption makes `toNat` an exact encoding of
length, and natural subtraction in the shifted inequality is the subtraction of finite
colengths. Source: Stacks Project, Algebra, Tag 00KQ, `proposition-dimension`, last
prime-chain paragraph (blueprint: lem-trf-prime-chain-bound-from-colength-polynomials).

Proof plan, following the node's eight steps:
1. By `lem-weil-pbc-local-ring-unit-criterion` (`IsLocalRing.notMem_maximalIdeal`),
   every proper ideal lies in `m`. Thus `p + (x)` is proper for `x` in `m`, and every
   positive-power colength of a proper quotient is at least one: its quotient is nonzero.
2. Identify `A_I / m_I^n` with `R / (I + m^n)`. Its `A_I`-submodules are exactly its
   `R`-submodules, by lifting scalars. For `I ≤ I'`, pull back strict submodule chains
   along the quotient surjection to get `H_I'(n) ≤ H_I(n)`. Length here is the supremum
   of chain lengths, as in `def-weil-pbc-module-length`.
3. For a polynomial `a T^d + sum (b_i T^i)` with `a > 0`, bound the lower terms at
   `n ≥ 1` by `B n^(d-1)`, where `B = sum |b_i|`. For `d ≥ 1` and `n ≥ 2B/a` this
   gives a lower bound `(a/2) n^d`; for `d = 0` the polynomial is the positive constant
   `a`. Thus an eventual inequality between nonzero polynomials with positive leading
   coefficients implies the degree inequality: otherwise their difference has positive
   leading coefficient and is eventually positive. Use `def-weil-polynomial-ring`.
4. For proper `I ≤ I'`, pass beyond their two individual equality thresholds in step 2
   and apply step 3. No uniform threshold across all ideals is needed.
5. Fix `p, x` and its shift `c ≥ 1`. Beyond the three thresholds for `Q_J(n)`, `Q_p(n)`
   and `Q_p(n-c)`, the hypothesis gives `Q_J(n) ≤ D(n)` for
   `D(T) = Q_p(T) - Q_p(T-c)`. Degree zero would give `D = 0`, contradicting step 1.
   For `d = deg Q_p ≥ 1`, the binomial expansion cancels the degree-`d` terms and gives
   degree `d-1` coefficient `d*c*lc(Q_p) > 0`; lower terms contribute smaller degrees.
   When `d = 1`, the lower constant terms have zero difference.
6. Apply step 3 to this eventual inequality to obtain `deg Q_J ≤ deg Q_p - 1`.
7. Given adjacent primes `p < q`, choose `x` in `q` outside `p`. It lies in `m`, and
   `J ≤ q`; steps 4 and 6 give a strict degree drop. Pull a strict prime chain in `R/I`
   back to primes containing `I` in `R`. Primality and strictness follow directly by
   lifting elements under the surjective quotient map.
8. Along a chain of length `r`, successive drops give `e_r + r ≤ e_0 ≤ deg Q_I`.
   This includes `r = 0` and degree zero. Take the supremum for `I = 0` to get the
   dimension bound, using `def-weil-pbc-krull-dimension-ring`.
-/
theorem primeChain_bound_of_colength_polynomials (R : Type u) [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (Q : Ideal R → Polynomial ℚ)
    (hfinite : ∀ (I : Ideal R), I ≠ ⊤ → ∀ (n : ℕ), 1 ≤ n →
      quotientPowerColength I n < ⊤)
    (hpoly : ∀ (I : Ideal R), I ≠ ⊤ →
      Q I ≠ 0 ∧ 0 < (Q I).leadingCoeff ∧
        ∃ N : ℕ, 1 ≤ N ∧ ∀ (n : ℕ), N ≤ n →
          ((quotientPowerColength I n).toNat : ℚ) = (Q I).eval (n : ℚ))
    (hdiff : ∀ (p : Ideal R), p.IsPrime → ∀ (x : R),
      x ∈ maximalIdeal R → x ∉ p → ∃ c : ℕ, 1 ≤ c ∧ ∀ (n : ℕ), c < n →
        (quotientPowerColength (p ⊔ Ideal.span {x}) n).toNat ≤
          (quotientPowerColength p n).toNat - (quotientPowerColength p (n - c)).toNat) :
    (∀ (I I' : Ideal R), I ≠ ⊤ → I' ≠ ⊤ → I ≤ I' →
      (Q I').natDegree ≤ (Q I).natDegree) ∧
    (∀ (p : Ideal R), p.IsPrime → ∀ (x : R), x ∈ maximalIdeal R → x ∉ p →
      1 ≤ (Q p).natDegree ∧ (Q (p ⊔ Ideal.span {x})).natDegree ≤ (Q p).natDegree - 1) ∧
    (∀ (I : Ideal R), I ≠ ⊤ → ∀ (s : LTSeries (PrimeSpectrum (R ⧸ I))),
      s.length ≤ (Q I).natDegree) ∧
    ringKrullDim R ≤ ((Q ⊥).natDegree : WithBot ℕ∞) := by
  sorry

end IsLocalRing
