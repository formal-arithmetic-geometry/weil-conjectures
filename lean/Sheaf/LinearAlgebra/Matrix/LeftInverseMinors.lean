/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.RingTheory.Ideal.Span
import Sheaf.LinearAlgebra.Matrix.CauchyBinet

/-!
# Scalar left inverses and maximal minors

Source: Stacks Project, Algebra, Lemma 07DQ and the Cauchy–Binet formula 0F0K
(blueprint: lem-weil-pbc-matrix-left-inverse-minors).
-/

@[expose] public section

universe u

namespace Matrix

/-- The ideal of maximal row minors gives scalar left inverses, and a scalar left inverse
puts the `m`-th power of its scalar in that ideal, with the explicit Cauchy–Binet expression.
Source: Stacks Project, Algebra, Lemma 07DQ and item 0F0K
(blueprint: lem-weil-pbc-matrix-left-inverse-minors).

Each subset of size `m` is enumerated in increasing order by `orderEmbOfFin`. The ideal is
written using `Ideal.span` of the range of these determinants. For `m = 0` the unique subset
is empty, its determinant is one, and this ideal is the whole ring.

Proof (the four steps of the node):
1. For each subset `I`, let `E_I` be the projection matrix selecting its rows. Entrywise
   multiplication gives `E_I * A = A_I` (def-weil-matrix, def-weil-submatrix).
2. For `f` in the span, write `f = ∑ I, c_I * det A_I`. Put
   `B = ∑ I, c_I • (adjugate A_I * E_I)`. The identity
   `adjugate A_I * A_I = det A_I • 1` (lem-weil-pbc-matrix-adjugate-identity)
   gives `B * A = f • 1`. For zero columns all these matrices are empty.
3. If `B * A = f • 1`, take determinants. The Leibniz expansion of the diagonal matrix
   `f • 1` gives `det (B * A) = f ^ m`, also for `m = 0` when both sides are one.
4. Apply lem-weil-pbc-cauchy-binet to `B` and `A`: the determinant of the product is the
   sum of the products of their corresponding column and row minors. These column minors
   are precisely the coefficients in the stated formula. It is an ideal combination of
   the generators, so `f ^ m` belongs to the span. -/
theorem scalar_left_inverse_maximal_minors {R : Type u} [CommRing R]
    (n m : ℕ) (_hmn : m ≤ n) (A : Matrix (Fin n) (Fin m) R) :
    let J : Ideal R := Ideal.span (Set.range
      (fun I : {I : Finset (Fin n) // I.card = m} ↦
        (A.submatrix (I.val.orderEmbOfFin I.property) id).det))
    (∀ f : R, f ∈ J → ∃ B : Matrix (Fin m) (Fin n) R, B * A = f • 1) ∧
      (∀ (f : R) (B : Matrix (Fin m) (Fin n) R), B * A = f • 1 →
        f ^ m ∈ J ∧
          f ^ m = ∑ I : {I : Finset (Fin n) // I.card = m},
            (B.submatrix id (I.val.orderEmbOfFin I.property)).det *
              (A.submatrix (I.val.orderEmbOfFin I.property) id).det) := by
  sorry

end Matrix
