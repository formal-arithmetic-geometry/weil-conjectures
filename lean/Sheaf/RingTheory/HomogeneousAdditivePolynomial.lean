module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import WeilConjectures.RingTheory.GradedAlgebra.Standard

import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Lucas
import WeilConjectures.Mathlib.Algebra.CharP.Lemmas

/-! # Monomial classification of homogeneous additive polynomials

Source: Dietel, A refinement of Hironaka's additive group schemes for an extended
invariant (2014), Proposition 3.3.5, printed pp.40–41, and Definition 1.4.1, p.17.
(blueprint: lem-trf-additive-polynomial-monomial-classification).

Additivity is an identity in the polynomial ring on two disjoint copies of the
variable tuple, rather than a condition only on points of the coefficient field.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace MvPolynomial

/-- A nonzero homogeneous polynomial of positive degree is formally additive
exactly when it is a linear form in characteristic zero, or a sum of pure powers
of a common characteristic-power degree in positive characteristic.

Source: Dietel (2014), Proposition 3.3.5, printed pp.40–41; Definition 1.4.1, p.17.
(blueprint: lem-trf-additive-polynomial-monomial-classification).

Proof:
1. From additivity, substitute zero to obtain f(0)=0, and split the variable
   tuple into its individual coordinates. Successive substitutions give
   f=sum_j f(0,...,Z_j,...,0). Homogeneity leaves only the monomials a_j Z_j^d
   (def-weil-pbc-mv-polynomial-ring, def-pc-standard-graded-algebra). If n=0,
   this forces f=0, contrary to the hypothesis. Otherwise some a_j is nonzero.
2. Restrict the two tuples to this coordinate. Expand (X+Y)^d using add_pow
   (lem-pur-commutative-ring-binomial-expansion). Comparing the coefficients
   of X^r Y^(d-r), for 0<r<d, and cancelling a_j gives (choose d r : k)=0.
3. In characteristic zero, r=1 rules out d>1. In positive characteristic p,
   the field axioms make p prime, and def-pc-field-characteristic turns these
   coefficient equations into p dividing choose d r. Apply
   lem-trf-binomial-vanishing-prime-power, recorded as
   Choose.eq_pow_multiplicity_of_choose_modEq_zero_nat, to get d=p^a.
4. Conversely, linear forms are additive by distributivity. In characteristic
   p, the a-fold Frobenius on the polynomial ring on both tuples is a ring
   homomorphism (def-weil-ring-frobenius, iterateFrobeniusOfPrime), giving
   (Z_j+W_j)^(p^a)=Z_j^(p^a)+W_j^(p^a). Multiply by a_j and sum. The case a=0
   is the identity Frobenius iterate and includes degree one. -/
theorem homogeneous_additive_monomial_classification
    {k : Type u} [Field k] (n d : ℕ) (f : MvPolynomial (Fin n) k)
    (hd : 0 < d) (hf : f ≠ 0) (hhom : f.IsHomogeneous d) :
    (ringChar k = 0 →
      ((aeval (fun j : Fin n ↦
          (X (Sum.inl j) : MvPolynomial (Fin n ⊕ Fin n) k) + X (Sum.inr j)) f =
        aeval (fun j : Fin n ↦ (X (Sum.inl j) : MvPolynomial (Fin n ⊕ Fin n) k)) f +
          aeval (fun j : Fin n ↦ (X (Sum.inr j) : MvPolynomial (Fin n ⊕ Fin n) k)) f) ↔
        d = 1 ∧ ∃ a : Fin n → k, f = ∑ j : Fin n, C (a j) * X j)) ∧
    (∀ p : ℕ, 0 < p → ringChar k = p →
      ((aeval (fun j : Fin n ↦
          (X (Sum.inl j) : MvPolynomial (Fin n ⊕ Fin n) k) + X (Sum.inr j)) f =
        aeval (fun j : Fin n ↦ (X (Sum.inl j) : MvPolynomial (Fin n ⊕ Fin n) k)) f +
          aeval (fun j : Fin n ↦ (X (Sum.inr j) : MvPolynomial (Fin n ⊕ Fin n) k)) f) ↔
        ∃ e : ℕ, d = p ^ e ∧
          ∃ a : Fin n → k, f = ∑ j : Fin n, C (a j) * X j ^ (p ^ e))) := by
  sorry

end MvPolynomial
