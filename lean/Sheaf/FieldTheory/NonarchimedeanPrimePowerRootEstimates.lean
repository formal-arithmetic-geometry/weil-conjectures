module

public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Order.Ring.IsNonarchimedean
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.RingTheory.Valuation.ValuationSubring

import Mathlib.RingTheory.WittVector.Frobenius
import Mathlib.Data.Nat.Choose.Sum

/-! # Nonarchimedean prime-power sum and root estimates

Source: Temkin, Stable modification of relative curves, Lemma 6.2.10(i)--(ii),
printed p. 46; the difference form follows by the same binomial estimate.
(blueprint: lem-trf-nonarchimedean-prime-power-root-estimates)
-/

@[expose] public section

set_option autoImplicit false

universe u

open scoped BigOperators

namespace AbsoluteValue

/-- Prime-power sums, differences, and arbitrary choices of roots satisfy the stated
nonarchimedean error bounds. The valuation subring `A` is specified exactly by `hA`,
so its residue field is the quotient of the closed unit ball by the open unit ball.
For the finite nonempty family, the real indexed supremum is its maximum.

Source: Temkin, Stable modification of relative curves, Lemma 6.2.10(i)--(ii),
printed p. 46, with the difference form from the same binomial estimate.
(blueprint: lem-trf-nonarchimedean-prime-power-root-estimates)

Proof plan:
1. The nonarchimedean inequality bounds the absolute value of every integer by one.
If an integer is divisible by `p`, its absolute value is at most `c = abv p`.
The residue quotient is a field, so its positive characteristic `p` is prime.
Consequently `q = p^n` is positive. If `n = 0`, all three errors are zero.
2. For `0 < j < q`, the p-adic order of `j` is less than `n`.
Apply lem-pur-prime-power-binomial-divisibility to deduce that `p` divides
`Nat.choose q j`. Expand the q-th power of a binary sum with
lem-pur-commutative-ring-binomial-expansion. Every interior term has absolute
value at most `c * max (abv a) (abv b)^q`. The finite-sum ultrametric bound
lem-trf-nonarchimedean-finite-sums gives the same bound on the binary error,
including when both elements vanish.
3. Induct on the number of summands. Each partial sum has absolute value at most
the maximum `M` of the input absolute values, by lem-trf-nonarchimedean-finite-sums.
Decompose the next error as the binary error plus the previous error; both are
bounded by `c * M^q`. The ultrametric inequality proves the first clause.
4. Apply the binary estimate to `a` and `-b`. For odd `p`, `q` is odd and this is
the difference clause. For `p = 2` and `n > 0`, include the extra term `2*b^q`;
its absolute value is at most `c * max (abv a) (abv b)^q` as well.
5. For any stipulated roots put `B = sum y_i` and `R = max (abv y_i)`.
Multiplicativity gives `R^q = max (abv x_i)`. The finite-sum bound gives
`abv B ≤ R` and `(abv y)^q ≤ R^q`, hence `abv y ≤ R`.
The first clause bounds `abv (B^q - y^q)` by `c*R^q`; the difference clause
bounds the difference between `(y-B)^q` and `y^q-B^q` by the same quantity.
Adding the errors gives `(abv (y-B))^q ≤ c*R^q`. Take nonnegative real q-th roots.
This also covers `R = 0` and `c = 0`, and does not assume roots exist.
-/
theorem nonarchimedean_prime_power_root_estimates
    {E : Type u} [Field E] (abv : AbsoluteValue E ℝ)
    (hna : IsNonarchimedean abv)
    (A : ValuationSubring E) (hA : ∀ z : E, z ∈ A ↔ abv z ≤ 1)
    (p : ℕ) (hp : 0 < p) [CharP (IsLocalRing.ResidueField A) p]
    (n t : ℕ) (ht : 0 < t) (x : Fin t → E) :
    abv ((∑ i : Fin t, x i) ^ (p ^ n) - ∑ i : Fin t, x i ^ (p ^ n)) ≤
        abv (p : E) * (⨆ i : Fin t, abv (x i)) ^ (p ^ n) ∧
      (∀ a b : E,
        abv ((a - b) ^ (p ^ n) - (a ^ (p ^ n) - b ^ (p ^ n))) ≤
          abv (p : E) * max (abv a) (abv b) ^ (p ^ n)) ∧
      (∀ (ys : Fin t → E) (y : E),
        (∀ i : Fin t, ys i ^ (p ^ n) = x i) →
        y ^ (p ^ n) = ∑ i : Fin t, x i →
        abv (y - ∑ i : Fin t, ys i) ≤
          abv (p : E) ^ (1 / ((p ^ n : ℕ) : ℝ)) *
            (⨆ i : Fin t, abv (x i)) ^ (1 / ((p ^ n : ℕ) : ℝ))) := by
  sorry

end AbsoluteValue
