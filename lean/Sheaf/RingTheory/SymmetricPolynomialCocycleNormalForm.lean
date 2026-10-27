/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q78
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Nat.Choose.Basic

/-! # Normal form for symmetric polynomial additive two-cocycles

Source: Milne, Algebraic Groups (2017), Lemma 15.26, printed p.316, and
Proposition 15.10 / Corollary 15.11, printed pp.308-309.
(blueprint: lem-sfb-symmetric-polynomial-cocycle-normal-form)
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace MvPolynomial

/-- Every normalized symmetric polynomial additive two-cocycle is a finite linear
combination of Frobenius powers of the Witt cocycle, modulo a polynomial coboundary.
The Witt cocycle is displayed explicitly: the natural-number division `p.choose j / p`
is performed before casting into the coefficient field. No perfection is assumed.

Source: Milne, Algebraic Groups (2017), Lemma 15.26, printed p.316, and
Proposition 15.10 / Corollary 15.11, printed pp.308-309.
(blueprint: lem-sfb-symmetric-polynomial-cocycle-normal-form)

Proof: Write delta b = b(X) + b(Y) - b(X+Y).
1. Split f into finitely many homogeneous components. Normalization, symmetry and
   the cocycle equation hold degreewise. Normalization kills degrees zero and one.
   Use strong induction on the degree n of a component
   h = sum_{i=1}^{n-1} u_i X^i Y^{n-i}, with u_i = u_{n-i}.
2. Set A = u_{n-1}. Comparing X^i Y^{n-1-i} Z in the cocycle equation gives
   (n-i) u_i = A binom(n-1,i).
3. If p does not divide n, apply this also at n-i and use symmetry to obtain
   i u_i = A binom(n-1,i-1). Addition gives n u_i = A binom(n,i).
   Thus h = delta (-(A/n) T^n), with zero constant term.
4. If n = p, put d_i = binom(p,i)/p in the integers. Primality makes this
   division exact for 0 < i < p. The integer identity
   (p-i)d_i = binom(p-1,i), followed by cancellation in k, gives u_i = A d_i.
   Therefore h = -A c_p; take a_0 = -A and b = 0. This includes p = 2.
5. If p divides n and n > p, take i = n-p in the recurrence. The binomial
   coefficient binom(n-1,p-1) reduces to 1, as seen by multiplying by (p-1)!
   and reducing the factors modulo p. Hence A = 0. The recurrence then kills
   u_i whenever p does not divide i. Both exponents of every surviving term
   are divisible by p.
6. Set m = n/p and g(U,V) = sum_j u_{pj} U^j V^{m-j}. Then h = g(X^p,Y^p).
   The freshman's dream and injectivity of the monomial substitution
   (U,V,W) = (X^p,Y^p,Z^p) show that g is again a normalized symmetric cocycle.
7. Apply induction to g. Substitution shifts each Frobenius exponent by one:
   c_p(X^p,Y^p) = c_p(X,Y)^p, since the coefficients of c_p are integer images.
   Replace b(T) by b(T^p); its constant term stays zero. No roots of the a_i
   are taken, so the argument applies to imperfect fields.
8. Pad the finitely many lists with zeros to a common last index and add them
   and their coboundaries. For f = 0 take r = 0, a_0 = 0 and b = 0.
All steps use only the field and characteristic definitions and the ordinary
univariate and multivariate polynomial operations recorded in the dependencies. -/
theorem symmetric_polynomial_cocycle_normal_form
    {k : Type u} [Field k] (p : ℕ) (hp : p.Prime) [CharP k p]
    (f : MvPolynomial (Fin 2) k)
    (hX : aeval ![(Polynomial.X : Polynomial k), 0] f = 0)
    (hY : aeval ![0, (Polynomial.X : Polynomial k)] f = 0)
    (hsym : aeval ![X (1 : Fin 2), X 0] f = f)
    (hcocycle :
      aeval ![(X 1 : MvPolynomial (Fin 3) k), X 2] f -
        aeval ![X (0 : Fin 3) + X 1, X 2] f +
        aeval ![X (0 : Fin 3), X 1 + X 2] f -
        aeval ![X (0 : Fin 3), X 1] f = 0) :
    ∃ (r : ℕ) (a : Fin (r + 1) → k) (b : Polynomial k),
      b.eval 0 = 0 ∧
      f = (∑ i : Fin (r + 1), C (a i) *
          (-∑ j ∈ Finset.Ioo 0 p,
            C ((p.choose j / p : ℕ) : k) * X (0 : Fin 2) ^ j * X 1 ^ (p - j)) ^
              (p ^ (i : ℕ))) +
        Polynomial.aeval (X (0 : Fin 2)) b + Polynomial.aeval (X (1 : Fin 2)) b -
        Polynomial.aeval (X (0 : Fin 2) + X 1) b := by
  sorry

end MvPolynomial
