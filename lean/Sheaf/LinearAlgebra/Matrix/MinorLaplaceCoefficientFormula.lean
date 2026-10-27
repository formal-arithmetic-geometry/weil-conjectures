module

public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.Finset.Sort
import Sheaf.GroupTheory.OrderedBlockPermutationSign

/-! # Laplace coefficient formula for a selected column set

Source: Stacks Project, Tag 07Z7, `lemma-ideals-generated-by-minors`, expansion hint;
the arbitrary-column-set coefficient calculation is supplied by the DAG proof.
(blueprint: lem-trf-minor-laplace-coefficient-formula)
-/

@[expose] public section

set_option autoImplicit false

universe u

open scoped BigOperators

namespace Matrix

/-- Expanding along the selected columns `T` gives the signed sum of complementary minors.
The summation subtype runs through every row set of cardinality `s` exactly once.
All four enumerations are increasing. The source label of `i : Fin q` is `i.val + 1`;
the integer sign is explicitly mapped to `R`.

Source: Stacks Project, Tag 07Z7, `lemma-ideals-generated-by-minors`, expansion hint;
the following arbitrary-column-set Leibniz grouping is agent-supplied.
(blueprint: lem-trf-minor-laplace-coefficient-formula)

Proof plan:
1. Apply `Matrix.det_apply'` [def-weil-pbc-matrix-determinant]. Group the permutations
   `σ` by the row set `I = σ(T)` and the permutations `α`, `β` induced on the increasing
   enumerations of the selected and complementary sets. Conversely, send the `a`-th
   selected column to the `α(a)`-th selected row, and the `b`-th complementary column
   to the `β(b)`-th complementary row. The two image sets are disjoint and exhaustive,
   so this gives a permutation; restriction recovers `I`, `α`, and `β` uniquely.
2. Apply `Equiv.Perm.sign_orderedBlocks` [lem-trf-ordered-block-permutation-sign] to
   this permutation. Its sign is the displayed integer power times the two induced
   permutation signs. Apply the canonical ring homomorphism from the integers to `R`.
3. Split each product of entries over `T` and its complement. Finite distributivity
   and commutativity factor the contribution for each `I` into the sign times the
   two Leibniz sums. By `Matrix.submatrix` [def-weil-submatrix] and `Matrix.det_apply'`,
   these sums are the two displayed determinants with increasing row and column orders.
4. If `s = 0`, only the empty row set contributes, with sign and selected determinant
   equal to one. If `s = q`, only the full row set contributes, its sign exponent is
   twice the sum of all labels, and the complementary determinant is one. If `q = 0`,
   necessarily `s = 0`, and both determinants and the sole contribution equal one.
   None of these steps uses cancellation, a nonzero ring, or invertible elements.
-/
theorem det_eq_sum_complementaryMinors {R : Type u} [CommRing R] {q s : ℕ}
    (_hs : s ≤ q) (Q : Matrix (Fin q) (Fin q) R) (T : Finset (Fin q))
    (hT : T.card = s) :
    Q.det = ∑ I : {I : Finset (Fin q) // I.card = s},
      (((-1 : ℤ) ^ ((∑ i ∈ I.val, (i.val + 1)) + ∑ j ∈ T, (j.val + 1))) : R) *
        (Q.submatrix (I.val.orderEmbOfFin I.property) (T.orderEmbOfFin hT)).det *
        (Q.submatrix
          ((I.valᶜ).orderEmbOfFin (k := q - s) (by simp [Finset.card_compl, I.property]))
          ((Tᶜ).orderEmbOfFin (k := q - s) (by simp [Finset.card_compl, hT]))).det := by
  sorry

end Matrix
