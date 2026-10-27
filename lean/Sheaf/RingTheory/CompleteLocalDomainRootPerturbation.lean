module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

import WeilConjectures.RingTheory.LocalDomainDimOnePrincipalLocalization
import Mathlib.GroupTheory.MonoidLocalization.Away

/-!
# Root perturbations over a complete one-dimensional local domain

Source: Stacks Project, More on Algebra, Tag 09EI, Lemma `lemma-krasner`, with precision
measured in powers of the chosen nonzero parameter
(blueprint: lem-sfb-complete-local-domain-root-perturbation).
-/

@[expose] public section

universe u

namespace Polynomial

/-- A root with nonzero derivative persists under sufficiently small coefficient perturbations,
with precision measured in powers of a prescribed nonzero element of the maximal ideal.
Source: Stacks Project, More on Algebra, Tag 09EI, Lemma `lemma-krasner` and its proof
(blueprint: lem-sfb-complete-local-domain-root-perturbation).

Proof:
1. Put `d = P.derivative.eval a`. The dimension-one localization theorem
   `lem-sc-local-domain-dim-one-principal-localization-fraction-field` identifies `R[1/t]`
   with the fraction field. The fraction description of `def-weil-ring-localization-away`
   then gives `v : R` and `M : ℕ` with `d * v = t ^ M`. Set `C = max c (M + 1)` and
   `n = M + C`, so `n ≥ 1`; these choices precede the choice of `Q`.
2. The finite-sum polynomial formula of `def-weil-polynomial-ring` gives Taylor identities
   `P(x+h) = P(x) + P'(x)h + h² A(x,h)` and `P'(x) - d = (x-a)B(x,a)`.
   The coefficient hypothesis gives `Q(x) ∈ t^n R` and `Q(x+h)-Q(x) ∈ t^n h R`, for any
   degree of `Q`.
3. For `F = P + Q`, start at `x_C = a` and inductively maintain `x_k-a ∈ t^C R` and
   `F(x_k) ∈ t^(M+k) R`. Write uniquely `F(x_k) = t^(M+k) e_k` using domain cancellation.
   Set `δ_k = -v t^k e_k` and `x_(k+1) = x_k + δ_k`. Then `δ_k ∈ t^k R` and
   `F(x_k) + d δ_k = 0`.
4. Taylor expansion leaves residual terms in `t^(C+k) R`, `t^(2k) R` and `t^(n+k) R`.
   Since `k ≥ C ≥ M+1` and `n ≥ M+1`, each belongs to `t^(M+k+1) R`, closing the induction.
   Only the fixed nonzero derivative was inverted in the fraction field.
5. Write `x_k-a = t^c y_k` uniquely. Cancellation gives
   `y_(k+1)-y_k ∈ t^(k-c) R`. Their classes modulo every power of the maximal ideal
   eventually stabilize compatibly. The inverse-limit bijection in
   `def-weil-pbc-adically-complete-ring` supplies their limit `y : R`. Put `b = a + t^c y`;
   then `b-a ∈ t^c R` without assuming that the principal ideal is closed.
6. For each `r`, sufficiently large `k` has both `b-x_k` and `F(x_k)` in the `r`-th power
   of the maximal ideal. The polynomial difference formula puts `F(b)` in the same power.
   Separatedness, included in `def-weil-pbc-adically-complete-ring`, gives `F(b) = 0`.
   The same `n` works for every allowed `Q`.
-/
theorem exists_root_add_of_isAdicComplete
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [IsDomain R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (hdim : ringKrullDim R = 1)
    (t : R) (ht_ne : t ≠ 0) (ht_mem : t ∈ IsLocalRing.maximalIdeal R)
    (P : Polynomial R) (a : R) (ha : P.eval a = 0) (hderiv : P.derivative.eval a ≠ 0) :
    ∀ c : ℕ, ∃ n : ℕ, 1 ≤ n ∧
      ∀ Q : Polynomial R, (∀ i : ℕ, t ^ n ∣ Q.coeff i) →
        ∃ b : R, (P + Q).eval b = 0 ∧ t ^ c ∣ b - a := by
  sorry

end Polynomial
