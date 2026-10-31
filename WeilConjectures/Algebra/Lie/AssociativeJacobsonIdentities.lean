/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Module.End
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Nat.Choose.Sum

/-!
# Jacobson identities for associative algebras

Source: Milne, Algebraic Groups (2017), Section 10k, Proposition 10.38(a),(b),
printed pp. 205–206 (blueprint: lem-sfb-associative-jacobson-identities).

The correction terms use the node's coefficient normalization, in the polynomial ring
with central indeterminate. The adjoint is expressed by Mathlib's left multiplication
minus right multiplication, so no second definition of the commutator is introduced.
-/

@[expose] public section

universe u v

set_option autoImplicit false

namespace Algebra

/-- The coefficient-normalized Jacobson correction term `sᵢ(a,b)` from Milne,
Section 10k, Proposition 10.38(b), printed pp. 205–206
(blueprint: lem-sfb-associative-jacobson-identities).

For `0 < i < p` in characteristic `p`, the scalar `(i : F)` is nonzero, so this
construction is exactly the unique term whose product by `i` is the coefficient
of `t^(i-1)` in `ad(ta+b)^(p-1)(a)`. The definition is total outside this range;
only the indicated range is used in the identity. -/
noncomputable def jacobsonCorrectionTerm (F : Type u) [Field F] {A : Type v}
    [Ring A] [Algebra F A] (p : ℕ) (a b : A) (i : ℕ) : A :=
  (i : F)⁻¹ •
    (Nat.iterate
      (fun q : Polynomial A ↦
        (Polynomial.X * Polynomial.C a + Polynomial.C b) * q -
          q * (Polynomial.X * Polynomial.C a + Polynomial.C b))
      (p - 1) (Polynomial.C a)).coeff (i - 1)

/-- Jacobson's two identities for an arbitrary associative unital algebra in prime
characteristic. Source: Milne, Algebraic Groups (2017), Section 10k,
Proposition 10.38(a),(b), printed pp. 205–206
(blueprint: lem-sfb-associative-jacobson-identities).

Proof plan from the node:
1. In the field (`def-weil-field`), the integers `1,...,p-1` are invertible.
   The factorial recurrences imply that the interior binomial coefficients of
   order `p` vanish and those of order `p-1` are alternating signs.
2. Left and right multiplication commute by associativity. Apply
   `Commute.add_pow` (`lem-sfb-commuting-binomial-expansion`) to their difference
   in the endomorphism ring and evaluate: `ad(z)^n(c)` is the alternating
   binomial sum of `z^(n-j) * c * z^j`.
3. At `n=p`, only the endpoint terms survive, giving the first identity.
   The sign is also correct at `p=2`, where minus equals plus.
4. In `A[t]`, set `z=ta+b`. At `n=p-1`, all signed binomial coefficients
   become one, giving the sum over all insertions of `a` among `p-1` copies of `z`.
5. The coefficientwise formal derivative satisfies the product rule without
   commuting coefficients. Induction on the power shows that the derivative
   of `z^p` is the insertion sum, hence `ad(z)^(p-1)(a)`.
6. The polynomial `Q=(ta+b)^p-t^p*a^p-b^p` has zero constant and degree-`p`
   coefficients and no higher terms. Comparing coefficients in its derivative
   gives `i*qᵢ=i*sᵢ`; cancel the invertible scalar `i`. Evaluating at the
   central scalar `t=1` gives the second identity. This uses formal coefficients,
   not polynomial-function detection over the possibly finite field. -/
theorem associative_jacobson_identities (F : Type u) [Field F] (A : Type v)
    [Ring A] [Algebra F A] (p : ℕ) [Fact p.Prime] [CharP F p] (a b : A) :
    (LinearMap.mulLeft F a - LinearMap.mulRight F a) ^ p =
        LinearMap.mulLeft F (a ^ p) - LinearMap.mulRight F (a ^ p) ∧
      (a + b) ^ p = a ^ p + b ^ p +
        ∑ i ∈ Finset.Ico 1 p, jacobsonCorrectionTerm F p a b i := by
  sorry

end Algebra
