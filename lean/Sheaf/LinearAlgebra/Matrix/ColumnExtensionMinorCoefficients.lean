/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Data.List.OfFn

/-!
# Recursive polynomial coefficients for column-extension minors

Source: Stacks Project, More on Algebra, Tag 07Z7, proof hint, iterated column expansion
(transposed from appended rows); agent-supplied recursive certificate
(blueprint: lem-trf-column-extension-minor-coefficients).

## Main definitions

* `Matrix.columnExtensionMinorPolynomial`: the list recursion in a fixed ambient alphabet.
* `Matrix.columnExtensionMinorCoefficient`: its specialization to size-indexed selections.

## Main statements

* `Matrix.det_submatrix_eq_sum_columnExtensionMinorCoefficient`: the evaluated identity.
-/

@[expose] public section

universe u

namespace Matrix

/-- The specified finite recursion, keeping a fixed ambient alphabet of matrix-entry symbols.
At depth zero it is the Kronecker delta on the two pairs of lists. At positive depth, remove
one row at a time and the last column, retaining order. On valid lists of common length `q`,
the sign is `(-1)^(a+q)` with row positions numbered from one. The empty-column branch is
irrelevant to valid positive-depth selections and makes the recursion total without choosing
an index in an empty ambient set. Keeping the ambient alphabet fixed identifies each smaller
polynomial with the same expression in the larger alphabet; only symbols whose columns remain
in the lists occur. Source: Stacks Project, More on Algebra, Tag 07Z7, proof hint, agent-supplied
iterated column expansion (blueprint: lem-trf-column-extension-minor-coefficients). -/
noncomputable def columnExtensionMinorPolynomial (p N : ℕ) :
    ℕ → List (Fin p) → List (Fin N) → List (Fin p) → List (Fin N) →
      MvPolynomial (Fin p × Fin N) ℤ
  | 0, I, J, U, V => if I = U ∧ J = V then 1 else 0
  | d + 1, I, J, U, V =>
      match J.getLast? with
      | none => 0
      | some j => ∑ a : Fin I.length,
          (-1) ^ (a.val + 1 + J.length) * MvPolynomial.X (I.get a, j) *
            columnExtensionMinorPolynomial p N d (I.eraseIdx a.val) J.dropLast U V

/-- The integer polynomial `L_d(I,J;U,V)` of the node, with the first `n` columns included
in `n+d` by `Fin.castAdd d`. No coefficients are chosen from ideal membership: this is the
literal finite recursion `columnExtensionMinorPolynomial`. Increasing lists are represented
by strictly monotone maps on `Fin`; the recursion itself is defined even before imposing
monotonicity. Source: Stacks Project, More on Algebra, Tag 07Z7, proof hint, agent-supplied
iterated column expansion (blueprint: lem-trf-column-extension-minor-coefficients). -/
noncomputable def columnExtensionMinorCoefficient (p n r d : ℕ)
    (I : Fin (r + d) → Fin p) (J : Fin (r + d) → Fin (n + d))
    (U : Fin r → Fin p) (V : Fin r → Fin n) : MvPolynomial (Fin p × Fin (n + d)) ℤ :=
  columnExtensionMinorPolynomial p (n + d) d (List.ofFn I) (List.ofFn J)
    (List.ofFn U) (List.ofFn (fun a ↦ Fin.castAdd d (V a)))

/-- Evaluating the specified recursive polynomials expresses every `(r+d)`-minor after
adjoining `d` columns as a sum of `r`-minors of the first `n` columns, all in increasing order.
Source: Stacks Project, More on Algebra, Tag 07Z7, proof hint, transposed to appended columns
(blueprint: lem-trf-column-extension-minor-coefficients).

Proof plan:
1. Fix `p,n,r`. At depth `d+1`, deleting the greatest selected column leaves all remaining
columns among the first `n+d`; deleting one row leaves a selection of size `r+d`. This also
covers a singleton selection, whose remaining lists are empty. Finite sums and products
preserve integer polynomials. The fixed ambient alphabet merely includes these expressions.
2. Induct on `d`. For `d=0` the Kronecker delta selects exactly `U=I,V=J`, giving the same
minor. For `r=0`, there is one pair of empty lists, and its determinant is one, by
`def-weil-pbc-matrix-determinant`.
3. For positive depth apply `lem-trf-minor-laplace-coefficient-formula` with the singleton
last position-column set. The selected row sets are singletons, their signs are `(-1)^(a+q)`,
and their determinants are the entries `B i_a j_q`. By `def-weil-submatrix`, the complementary
minors are precisely the ordered deletions used in the recursion.
4. Apply the induction hypothesis to the first `n+d-1` columns of `B`. Its first `n` columns
are still `A`. Substitute these identities in the column expansion and interchange the finite
sums. Polynomial evaluation preserves addition and multiplication, so the resulting coefficient
is exactly the recursion evaluated at `B`. No division is used, so this works in every
commutative ring. Empty selection types make the assertion vacuous. -/
theorem det_submatrix_eq_sum_columnExtensionMinorCoefficient
    {R : Type u} [CommRing R] (p n r d : ℕ) (B : Matrix (Fin p) (Fin (n + d)) R)
    (I : Fin (r + d) → Fin p) (J : Fin (r + d) → Fin (n + d))
    (hI : StrictMono I) (hJ : StrictMono J) :
    (B.submatrix I J).det =
      ∑ U ∈ (Finset.univ : Finset (Fin r → Fin p)).filter StrictMono,
        ∑ V ∈ (Finset.univ : Finset (Fin r → Fin n)).filter StrictMono,
          MvPolynomial.eval₂ (Int.castRingHom R) (fun ij ↦ B ij.1 ij.2)
              (columnExtensionMinorCoefficient p n r d I J U V) *
            ((B.submatrix id (Fin.castAdd d)).submatrix U V).det := by
  sorry

end Matrix
