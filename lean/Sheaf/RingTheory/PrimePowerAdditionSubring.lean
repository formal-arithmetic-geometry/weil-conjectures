/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.RingTheory.WittVector.Frobenius

/-!
# Addition and prime-power subring membership

Source: Stacks Project, Algebra, Tag 0545, `lemma-help-with-powers`, evaluated in an
arbitrary commutative ring (blueprint: lem-pur-prime-power-addition-subring).
-/

@[expose] public section

universe u

namespace Subring

/-- (blueprint: lem-pur-prime-power-addition-subring) Stacks Project, Algebra, Tag 0545,
`lemma-help-with-powers`, evaluated in a commutative ring. If a unital subring contains
prime-power powers and the corresponding prime-power multiples of `x` and `y`, it contains
such a power and multiple of their sum, with the same positive exponent.

Proof plan:
1. Choose `a = n * p ^ n + m * p ^ m + n + m`. It is positive and at least `n` and `m`.
   Put `B = n * (p ^ n - 1) + m * (p ^ m - 1)`. Both `a - n + 1` and `a - m + 1`
   are at least `B`. The subring contains all integer multiples of `1`, so the identity
   `p^a(x+y) = p^(a-n)(p^n x) + p^(a-m)(p^m y)` gives the required multiple membership.
2. Expand `(x+y)^(p^a)` by `add_pow` (lem-pur-commutative-ring-binomial-expansion).
   For an index `i`, put `j = p^a - i` and write `i = q*p^n + r`, `j = q'*p^m + r'`
   with `r < p^n` and `r' < p^m`. Put `D = n*r + m*r'`, so `D ≤ B`.
3. If both remainders vanish, divisibility of the binomial coefficient by `p^D` is trivial.
   If `r > 0`, then `i > 0` and `v_p(i) ≤ n-1`. Apply
   `WittVector.map_frobeniusPoly.key₁` (lem-pur-prime-power-binomial-divisibility):
   `p^(a-v_p(i))` divides the coefficient, and `D ≤ B ≤ a-n+1 ≤ a-v_p(i)`.
   Otherwise use `j > 0`, `v_p(j) ≤ m-1`, and symmetry of binomial coefficients.
   At `i = 0` and `i = p^a`, both remainders vanish since `a ≥ n,m`.
4. Write each coefficient as `c * p^(n*r+m*r')`. Its term is
   `c * (x^(p^n))^q * (y^(p^m))^q' * (p^n*x)^r * (p^m*y)^r'`.
   All four bases lie in the subring by hypothesis; closure under powers, products,
   integer multiples, and finite sums proves the power membership. No cancellation
   or division in the ambient ring is needed. -/
theorem exists_prime_pow_add_mem {C : Type u} [CommRing C] (A : Subring C)
    {p : ℕ} (hp : p.Prime) {x y : C} {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (hx : x ^ (p ^ n) ∈ A) (hpx : (p : C) ^ n * x ∈ A)
    (hy : y ^ (p ^ m) ∈ A) (hpy : (p : C) ^ m * y ∈ A) :
    ∃ a : ℕ, 0 < a ∧ (x + y) ^ (p ^ a) ∈ A ∧ (p : C) ^ a * (x + y) ∈ A := by
  sorry

end Subring
