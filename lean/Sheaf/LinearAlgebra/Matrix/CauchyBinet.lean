/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.Powerset

/-!
# The Cauchy–Binet formula

Source: Stacks Project, Algebra, Section 00AR, item 0F0K
(blueprint: lem-weil-pbc-cauchy-binet).
-/

@[expose] public section

universe u

namespace Matrix

/-- The Cauchy–Binet formula, including its empty-sum and zero-size cases.
Source: Stacks Project, Algebra, Section 00AR, item 0F0K
(blueprint: lem-weil-pbc-cauchy-binet).

The subsets of size `m` are enumerated once each. For each subset, `orderEmbOfFin` lists
its indices in increasing order, and the same list selects columns of `A` and rows of `B`.

Proof (the five steps of the node):
1. Expand the Leibniz formula for `det (A * B)` using the entries of the matrix product.
   Distribute the products over the finite sums to obtain a sum over maps `f : Fin m → Fin n`
   of `(∏ k, B (f k) k) * det (A.submatrix id f)`
   (def-weil-pbc-matrix-determinant and def-weil-matrix).
2. Noninjective maps give repeated columns, so their determinants vanish by
   lem-weil-pbc-det-repeated-column-zero; retain only injective maps.
3. Each injective map is uniquely an increasing enumeration of its image subset followed
   by a permutation of `Fin m`. Thus group the terms by subsets of size `m` and permutations.
4. The column permutation multiplies the determinant of the selected columns by its sign
   (lem-weil-pbc-det-column-permutation). The other factor is the product of entries of
   the selected rows of `B` (def-weil-submatrix).
5. Sum over the permutations using the Leibniz formula to obtain the determinant of the
   selected rows of `B`, and factor out the determinant of the selected columns of `A`
   (def-weil-pbc-matrix-determinant). If `n < m`, no subset exists and the sum is zero.
   If `m = 0`, only the empty subset exists, and both empty determinants are one. -/
theorem cauchy_binet {R : Type u} [CommRing R] (m n : ℕ)
    (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin n) (Fin m) R) :
    let minors : R := ∑ S : {S : Finset (Fin n) // S.card = m},
      (A.submatrix id (S.val.orderEmbOfFin S.property)).det *
        (B.submatrix (S.val.orderEmbOfFin S.property) id).det
    (A * B).det = minors ∧
      (n < m → minors = 0 ∧ (A * B).det = 0) ∧
      (m = 0 → (A * B).det = 1 ∧ minors = 1) := by
  sorry

end Matrix
