module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-! # Divisibility by distinct hyperplane equations

Source: Stacks Project, `algebra.tex`, Tag 0BC1, lemma-polynomial-ring-UFD;
the coordinate restriction and homogeneity corollary are the agent-formulated
statement (blueprint: lem-sfb-distinct-hyperplane-polynomial-divisibility).
-/

@[expose] public section

set_option autoImplicit false

universe u

open scoped BigOperators

namespace MvPolynomial

/-- A polynomial vanishing on finitely many distinct linear hyperplanes is
divisible by the product of their equations. In the degree range at or below
the number of hyperplanes, the homogeneous cases are forced as stated.

Source: Stacks Project, `algebra.tex`, Tag 0BC1, lemma-polynomial-ring-UFD;
the coordinate restriction and homogeneity argument are the agent-formulated
corollary. (blueprint: lem-sfb-distinct-hyperplane-polynomial-divisibility)

Proof plan:
1. Set D_j to the product of the first j equations, with D_0 = 1.
   By lem-sfb-polynomial-field-ufd the polynomial ring is a domain, so all
   prefix products are nonzero. With no variables there are no nonzero
   degree-one equations, hence m = 0, and only scalar polynomials remain.
2. For a nonzero linear equation ell = sum a_t x_t choose a_j nonzero.
   In the ring A of the remaining variables put b = -a_j⁻¹ sum_{t ≠ j} a_t x_t.
   Substitution x_j = b restricts a polynomial F to Fbar in A. Expanding in
   powers of x_j and using x_j^n - b^n = (x_j - b) sum_{s < n} x_j^(n-1-s) b^s
   gives F - Fbar = (x_j - b) T. Since ell = a_j (x_j - b), Fbar = 0
   if and only if ell divides F. Vanishing on the hyperplane makes Fbar vanish
   on every assignment; lem-sfb-mvpolynomial-infinite-evaluation, namely
   `MvPolynomial.funext`, gives Fbar = 0, also when A has no variables.
3. Inductively write P = D_j Q_j, starting with Q_0 = P. Restrict to the next
   hyperplane. Every earlier equation remains nonzero: if sum c_t x_t restricts
   to zero, its coefficients give c_t = c_j a_t / a_j for t ≠ j, making it a
   scalar multiple of the next equation. The scalar is nonzero since the earlier
   equation is nonzero, contrary to nonproportionality. The domain clause of
   lem-sfb-polynomial-field-ufd now makes D_j's restriction nonzero. P restricts
   to zero, so Q_j restricts to zero. Step 2 gives Q_j = ell_{j+1} Q_{j+1}.
   At j = m this is the required product divisibility.
4. If P = 0 take scalar c = 0 in the equality case. Otherwise P = D_m Q with
   Q nonzero. Each equation has total degree one, hence repeated use of
   lem-sfb-mvpolynomial-total-degree-product gives totalDegree D_m = m.
   A nonzero degree-d homogeneous P has total degree d, so the same lemma gives
   d = m + totalDegree Q. Thus d < m is impossible. If d = m, Q has total
   degree zero; every supported exponent is zero, so Q = C c for some scalar c.
   This includes m = 0 and D_0 = 1.
-/
theorem distinct_hyperplane_polynomial_divisibility
    {k : Type u} [Field k] [Infinite k]
    (r m d : ℕ)
    (ell : Fin m → MvPolynomial (Fin r) k)
    (hell_nonzero : ∀ i : Fin m, ell i ≠ 0)
    (hell_homogeneous : ∀ i : Fin m, (ell i).IsHomogeneous 1)
    (hell_nonproportional :
      ∀ i j : Fin m, i ≠ j → ∀ c : k, c ≠ 0 → ell i ≠ C c * ell j)
    (P : MvPolynomial (Fin r) k)
    (hvanish :
      ∀ i : Fin m, ∀ a : Fin r → k,
        eval a (ell i) = 0 → eval a P = 0) :
    (∏ i : Fin m, ell i) ∣ P ∧
      (∏ i : Fin m, ell i) ≠ 0 ∧
      (P.IsHomogeneous d →
        (d < m → P = 0) ∧
          (d = m → ∃ c : k, P = C c * ∏ i : Fin m, ell i)) := by
  sorry

end MvPolynomial
