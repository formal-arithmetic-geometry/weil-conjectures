/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q142
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Degrees

import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.MvPolynomial.Funext

/-! # Polynomial interpolation from uniformly bounded affine-line restrictions

Source: Milne, Abelian Varieties, Chapter I, Lemma 10.12, printed p.47, with the uniform
bound supplied by Proposition 10.13, printed pp.47-48; bounded version and total-degree
argument (blueprint: lem-sfb-bounded-line-polynomial-interpolation).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open scoped BigOperators

namespace MvPolynomial

/-- Uniformly bounded polynomial restrictions to affine lines give a polynomial of the same
bounded total degree on every finite tuple of vectors. Polynomial evaluation on all tuples
also determines the polynomial, with no degree restriction on this determination clause.

Source: Milne, Abelian Varieties, Chapter I, Lemma 10.12 proof, printed p.47, using the uniform
bound from Proposition 10.13; bounded version and total-degree argument.
(blueprint: lem-sfb-bounded-line-polynomial-interpolation)

Proof plan:
1. Choose distinct c_0,...,c_D in the infinite field. Induct on n, simultaneously for all
   translates w, to represent F(w + sum x_i e_i) by a polynomial with degree at most D in
   each variable. For n = 0 use the constant F(w), including the no-variable case of
   def-weil-pbc-mv-polynomial-ring.
2. At the induction step interpolate the polynomials obtained at translates w + c_j e_n
   with the Lagrange basis in the final variable. The affine-line hypothesis and
   lem-sfb-lagrange-reconstruction identify this interpolation with F at every point.
   The coefficient expansion in def-weil-pbc-mv-polynomial-ring bounds each separate
   variable degree by D, even for zero or repeated vectors.
3. Prove determination by induction on the number of variables: collect coefficients
   in the final variable. At each assignment of the other variables the resulting
   univariate polynomial vanishes everywhere, hence is zero by
   lem-trf-polynomial-infinite-evaluation-identity. Induction kills each coefficient.
   For no variables the sole value is the constant coefficient.
4. Apply the translated construction at w = 0. If its polynomial has total degree m > D,
   its nonzero top homogeneous part has a nonvanishing direction by
   lem-trf-infinite-field-top-form-direction. Substitution of this direction times T
   gives a univariate polynomial of degree m. Its values agree with the degree-at-most-D
   affine-line polynomial for the corresponding vector sum in W. The identity lemma
   forces equality, a contradiction. The zero polynomial and the no-variable case
   already have total degree at most D. -/
theorem exists_of_bounded_affine_lines
    {K : Type u} [Field K] [Infinite K]
    {W : Type v} [AddCommGroup W] [Module K W]
    (D : ℕ) (F : W → K)
    (hF : ∀ v w : W, ∃ q : Polynomial K,
      q.natDegree ≤ D ∧ ∀ t : K, F (t • v + w) = q.eval t) :
    (∀ (r : ℕ) (e : Fin r → W), ∃ P : MvPolynomial (Fin r) K,
      P.totalDegree ≤ D ∧
        ∀ x : Fin r → K, F (∑ i : Fin r, x i • e i) = MvPolynomial.eval x P) ∧
    (∀ (r : ℕ) (P Q : MvPolynomial (Fin r) K),
      (∀ x : Fin r → K, MvPolynomial.eval x P = MvPolynomial.eval x Q) → P = Q) := by
  sorry

end MvPolynomial
