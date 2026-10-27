module

public import Mathlib.Algebra.Lie.OfAssociative
public import Sheaf.Algebra.Lie.KostantIntegralForm
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Divided-power straightening for an associative sl2 triple

Source: Milne, Algebraic Groups (2017), Section 23h, printed pp. 508–510, for the
rank-one and admissible-lattice motivation; the explicit associative induction in the DAG
(blueprint: lem-sfb-sl2-divided-straightening).

The bracket is the ring commutator. The three relations are imposed separately, so the zero
triple is allowed. The divided powers and falling binomials are the existing rational-algebra
constructions, with factorial denominators acting by rational scalar multiplication.
-/

@[expose] public section

universe u

namespace Algebra

/-- The divided-power normal-ordering identity for three elements of any associative unital
rational algebra with the sl2 commutator relations. No nonzero or finiteness condition is needed.
Source: Milne, Algebraic Groups (2017), Section 23h, printed pp. 508–510, motivating the integral
PBW calculation (blueprint: lem-sfb-sl2-divided-straightening).

Proof (the explicit associative calculation recorded in the DAG, not a proof quoted from Milne):
1. By `def-wf-lie-algebra`, the associative bracket is `XY - YX`. Rational scalars are central.
   Write `B_t(X) = X(X-1)...(X-t+1)/t!`, with `B_0 = 1`. The relations imply
   `EH = (H-2)E` and `HF = F(H-2)`, and `E E^(a)/(a!) = (a+1) E^(a+1)/(a+1)!`.
2. Induction on `j` gives `HF^j = F^j(H-2j)`. Applying `E(H+c-i) = (H+c-i-2)E`
   to each falling-product factor gives `E B_t(H+c) = B_t(H+c-2)E`, also at `t = 0`.
3. Telescope `EF^r - F^rE` into the sum of `F^i(EF-FE)F^(r-1-i)`.
   The preceding shift makes this `r F^(r-1)(H-r+1)`, using
   `2 sum_{j<r} j = r(r-1)`. For `r > 0` divide by `r!` to obtain
   `E F^(r)/r! = (F^r/r!) E + (F^(r-1)/(r-1)!)(H-r+1)`.
   For `r = 0`, only the first term occurs.
4. Falling products give `t B_t(X) = (X-t+1) B_(t-1)(X)` and
   `B_t(X+1) - B_t(X) = B_(t-1)(X)` for positive `t`: factor out the common
   product in the difference, leaving the scalar `t`. Therefore
   `(m+1-t) B_t(X) + (X+m-t+2) B_(t-1)(X) = (m+1) B_t(X+1)`.
   These polynomial identities may be evaluated at `H` plus a scalar.
5. Fix `n` and induct on `m`. For `m = 0` the single summand is `F^n/n!`.
   Multiply the inductive equality on the left by `E` and divide by the nonzero rational
   `m+1`. Expand by distributivity; no linear-independence assumption is used.
6. Put `C_t = H-m-n+2t`. The first contribution of an old summand is
   `((m-t+1)/(m+1)) F^((n-t)) B_t(C_t-2) E^((m-t+1))`, where double
   parentheses denote divided powers. When `t < n` the second contribution is
   `(1/(m+1)) F^((n-t-1)) (H-n+t+1) B_t(C_t) E^((m-t))`.
   At `t = n` it is absent. Only rational scalars and polynomials in `H` are commuted.
7. Reindex the second contribution by old index `t-1`. With `X = H-m-n+2t-2`,
   the common outer factors are `F^((n-t))` and `E^((m+1-t))`. The middle factor is
   `((m+1-t) B_t(X) + (X+m-t+2) B_(t-1)(X))/(m+1) = B_t(X+1)` by Step 4.
   Since `X+1 = H-(m+1)-n+2t`, this is the required successor summand.
8. At `t = 0` only the first contribution occurs and its coefficient is one.
   At `t = m+1` the missing first contribution has coefficient zero. No second term
   arises beyond `t = n`, and no term exceeds `m+1`. Thus the range is exactly
   `0 ≤ t ≤ min (m+1) n`, including `n = 0`. This finishes the induction using
   only the three relations, associativity, distributivity, and rational scalar arithmetic. -/
theorem sl2_dividedPower_straightening
    (A : Type u) [Ring A] [Algebra ℚ A] (E F H : A)
    (hEF : ⁅E, F⁆ = H) (hHE : ⁅H, E⁆ = 2 * E) (hHF : ⁅H, F⁆ = -(2 * F))
    (m n : ℕ) :
    rationalDividedPower E m * rationalDividedPower F n =
      ∑ t ∈ Finset.range (min m n + 1),
        rationalDividedPower F (n - t) *
          rationalBinomial (H - (m : A) - (n : A) + 2 * (t : A)) t *
          rationalDividedPower E (m - t) := by
  sorry

end Algebra
