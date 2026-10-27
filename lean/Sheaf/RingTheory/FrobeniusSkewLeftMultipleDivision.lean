module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.SkewPolynomial.Basic

/-! # Division by left multiples in the Frobenius skew-polynomial ring

Source: Milne, Algebraic Groups (2017), printed p.296, the right division algorithm
immediately before Proposition 14.50
(blueprint: lem-sfb-frobenius-skew-left-multiple-division).

Mathlib encodes the twisting endomorphism by a `MulSemiringAction (Multiplicative ℕ) k`.
The condition on its generator `φ` specifies the Frobenius twist, hence precisely the
multiplication `(a F^i) (b F^j) = a b^(p^i) F^(i+j)`. For nonzero polynomials,
`support.sup id` is their degree. No perfectness or surjectivity of Frobenius is assumed.
-/

@[expose] public section

universe u

namespace SkewPolynomial

/-- Division by a left multiple in the Frobenius skew-polynomial ring over any field
of prime characteristic.

Source: Milne, Algebraic Groups (2017), printed p.296, right division algorithm
immediately before Proposition 14.50
(blueprint: lem-sfb-frobenius-skew-left-multiple-division).

Proof plan: fix nonzero g of degree m and leading coefficient b. Use strong induction
on N(f), where N(0) = 0 and N(f) = deg(f) + 1 for nonzero f. For f = 0 choose q = r = 0.
If f is nonzero of degree less than m, choose q = 0 and r = f.

Otherwise write n = deg(f), a for its leading coefficient, and d = n - m. By the field
axioms (def-weil-field), b^(p^d) is nonzero. Put c = a * (b^(p^d))⁻¹ and u = c F^d.
The specified Frobenius twist, `φ_iterate_apply`, and `monomial_mul_monomial` give
u g = ∑ j, c * g_j^(p^d) F^(d+j). Its leading coefficient is a in degree n, and all
coefficients above n vanish. This uses inversion only, without extracting roots.

Thus h = f - u g is zero or has degree less than n, so N(h) < N(f). When n = 0 the
same coefficient calculation gives h = 0, without taking the degree of zero. Apply
induction to write h = q₁ g + r with the required remainder bound. Distributivity gives
f = u g + h = (u + q₁) g + r, so choose q = u + q₁. If m = 0, the remainder must be
zero because the degree of a nonzero polynomial is a natural number. -/
theorem exists_frobenius_left_multiple_division {k : Type u} [Field k]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP k p]
    [MulSemiringAction (Multiplicative ℕ) k]
    (hF : ∀ a : k, SkewPolynomial.φ a = a ^ p)
    (f g : SkewPolynomial k) (hg : g ≠ 0) :
    ∃ q r : SkewPolynomial k,
      f = q * g + r ∧ (r = 0 ∨ r.support.sup id < g.support.sup id) := by
  sorry

end SkewPolynomial
