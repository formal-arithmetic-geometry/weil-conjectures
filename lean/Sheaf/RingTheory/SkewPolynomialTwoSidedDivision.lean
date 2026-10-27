module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.SkewPolynomial.Basic

/-! # Division on both sides in an automorphism skew-polynomial ring

Source: Milne, Algebraic Groups (2017), printed p.296, division algorithms before and after
Proposition 14.50 (blueprint: lem-sfb-skew-polynomial-two-sided-division).

The coefficient automorphism is the generator `SkewPolynomial.φ` of the semiring action;
its bijectivity is the automorphism hypothesis. For a nonzero polynomial, `support.sup id`
is the largest index of a nonzero coefficient. The zero remainder is allowed separately.
-/

@[expose] public section

universe u

namespace SkewPolynomial

/-- Division on both sides with a remainder of smaller degree.

Source: Milne, Algebraic Groups (2017), printed p.296, division algorithms before and after
Proposition 14.50 (blueprint: lem-sfb-skew-polynomial-two-sided-division).

Proof plan: write σ for `φ`, fix nonzero g of degree m and leading coefficient b, and use
simultaneous strong induction on the degree n of nonzero f. If f = 0, take all four outputs
zero. If n < m, take both quotients zero and both remainders f. Otherwise put d = n - m and
write a for the leading coefficient of f. The field inverses are supplied by def-weil-field.

For the left multiple, set c = a / σ^d(b), which is defined with nonzero denominator because
σ is injective. The monomial t = c F^d makes the leading coefficient of t g equal to a.
Thus h = f - t g is zero or has degree less than n. In the zero case use quotient t and
remainder zero; otherwise apply induction to h = u g + r and obtain f = (t + u) g + r.

For the right multiple, bijectivity gives c = σ^(-m)(b^(-1) a). With t = c F^d, the leading
coefficient of g t is b σ^m(c) = a. Again h = f - g t is zero or has degree less than n.
In the zero case use quotient t and remainder zero; otherwise apply induction to h = g u + r
and obtain f = g (t + u) + r. The multiplication formula follows from
`SkewPolynomial.monomial_mul_monomial` and distributivity in both cases.

Both recursive calls have strictly smaller degree. If n = m = 0, each difference has all
coefficients zero, so the constant-divisor base case is included. The independent choices
on the two sides yield the four asserted polynomials and both remainder bounds. -/
theorem exists_two_sided_division {k : Type u} [Field k]
    [MulSemiringAction (Multiplicative ℕ) k]
    (hσ : Function.Bijective (SkewPolynomial.φ (R := k)))
    (f g : SkewPolynomial k) (hg : g ≠ 0) :
    ∃ qL rL qR rR : SkewPolynomial k,
      f = qL * g + rL ∧ f = g * qR + rR ∧
      (rL = 0 ∨ rL.support.sup id < g.support.sup id) ∧
      (rR = 0 ∨ rR.support.sup id < g.support.sup id) := by
  sorry

end SkewPolynomial
