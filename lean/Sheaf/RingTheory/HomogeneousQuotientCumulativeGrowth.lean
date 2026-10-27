/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q109
-/
module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Degree.Defs
import WeilConjectures.RingTheory.GradedAlgebra.Standard
import Sheaf.RingTheory.StandardGradedHilbertFunction
import WeilConjectures.Mathlib.Algebra.Group.ForwardDiff
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.Analysis.Polynomial.Basic

/-! # Cumulative Hilbert growth of a homogeneous polynomial quotient

Source: Stacks Project, Algebra, Tags 00K3 (lemma-quotient-smaller-d) and 00JZ
(lemma-numerical-polynomial), in cumulative form
(blueprint: lem-sfb-homogeneous-quotient-cumulative-growth).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace MvPolynomial

/-- A nonzero proper homogeneous ideal lowers cumulative Hilbert growth below the number
of variables. The graded pieces are the images of the actual homogeneous subspaces in the
actual quotient, and they form an internal direct sum and are finite-dimensional.

Source: Stacks Project, Algebra, Tags 00K3 and 00JZ
(blueprint: lem-sfb-homogeneous-quotient-cumulative-growth).

Proof (the node's eight steps):
1. Homogeneity gives the direct-sum decomposition of the ideal and hence of its quotient.
Each polynomial homogeneous piece has a finite monomial basis, whose images span the
quotient piece. Properness excludes nonzero constants in the ideal, so the degree-zero
quotient piece is k and every positive cumulative value is at least one.
2. The polynomial ring is standard graded and its quotient is a cyclic graded module.
Apply lem-trf-standard-graded-hilbert-function to obtain an eventual rational polynomial A
for the dimensions of the individual pieces, with threshold n0 at least one; A may be zero.
3. Set F(t) equal to the cumulative dimension at n0+t. Its forward difference is A(n0+t).
Apply lem-trf-rational-sequence-polynomial-forward-difference, using degree bound zero
when A is zero and deg A+1 otherwise. Translating its polynomial back gives Q and
Q(n) equal to the cumulative dimension for every n at least n0.
4. Some homogeneous component f of a nonzero element of the ideal is nonzero and remains
in the ideal. Its degree e is positive, since a nonzero constant would contradict properness.
5. The subspace V_n of polynomials of degree less than n has dimension binomial(n+d-1,d):
count exponent tuples by adjoining a slack entry and using stars and bars. Thus its dimension
is B(n), where B(X)=X(X+1)...(X+d-1)/d!, also when n=1 or d=1.
6. By lem-weil-pbc-polynomial-ring-domain, multiplication by f injects V_(n-e) into
I intersect V_n for n at least e+1. Apply lem-trf-vector-space-quotient-dimension to
V_n/(I intersect V_n), the sum of the first n quotient pieces. Its dimension is at most
B(n)-B(n-e).
7. D(X)=B(X)-B(X-e) has degree d-1 and positive leading coefficient e/(d-1)! by
cancellation of its degree-d coefficients. For d=1 it is the positive constant e.
Thus eventually 1 <= Q(n) <= D(n).
8. The lower bound excludes Q=0. Apply lem-sfb-polynomial-leading-term-asymptotic with
epsilon=1/2: a negative leading coefficient would contradict the lower bound. The same
asymptotic estimate for Q and D shows deg Q < d, since otherwise their ratio grows without
bound. Take N=n0, retaining the same Q for equality, positivity and the degree bound. -/
theorem exists_polynomial_cumulative_growth_of_homogeneous_ideal
    {k : Type u} [Field k] {d : ℕ} (hd : 1 ≤ d)
    (I : Ideal (MvPolynomial (Fin d) k)) (hne : I ≠ ⊥) (hproper : I ≠ ⊤)
    (hhom : ∀ f : MvPolynomial (Fin d) k, f ∈ I →
      ∀ j : ℕ, homogeneousComponent j f ∈ I) :
    DirectSum.IsInternal (fun j : ℕ ↦
      (homogeneousSubmodule (Fin d) k j).map (Ideal.Quotient.mkₐ k I).toLinearMap) ∧
    (∀ j : ℕ, Module.Finite k
      ((homogeneousSubmodule (Fin d) k j).map (Ideal.Quotient.mkₐ k I).toLinearMap)) ∧
    ∃ Q : Polynomial ℚ, Q ≠ 0 ∧ 0 < Q.leadingCoeff ∧ Q.natDegree < d ∧
      ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
        ((∑ j ∈ Finset.range n, Module.finrank k
          ((homogeneousSubmodule (Fin d) k j).map (Ideal.Quotient.mkₐ k I).toLinearMap)) : ℚ) =
          Q.eval (n : ℚ) := by
  sorry

end MvPolynomial
