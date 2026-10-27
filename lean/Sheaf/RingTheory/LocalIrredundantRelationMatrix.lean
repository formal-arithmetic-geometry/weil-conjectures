module

public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Relation matrices of irredundant tuples over local rings

Source: Stacks Project, Algebra, Tag 0592, `lemma-projective-freeness-criteria`,
last paragraph of the proof (blueprint: lem-trf-local-irredundant-relation-matrix).
-/

@[expose] public section

universe u

namespace IsLocalRing

/-- A matrix fixing an irredundant tuple is congruent to the identity modulo the maximal
ideal, has unit determinant, and admits a two-sided inverse.

Source: Stacks Project, Algebra, Tag 0592, `lemma-projective-freeness-criteria`,
last paragraph of the proof (blueprint: lem-trf-local-irredundant-relation-matrix).

Proof:
1. Rearrange the column relation to express `(1 - B j j) * a j` as a linear combination
   of the other entries. If `1 - B j j` were a unit, division would contradict
   irredundancy. The local-ring unit criterion (lem-weil-pbc-local-ring-unit-criterion)
   puts it in the maximal ideal. Since that ideal is proper, `B j j` is outside it
   and is a unit by the same criterion.
2. If `B i j` were a unit for distinct `i, j`, solve the column relation for `a i`.
   This again contradicts irredundancy, so the unit criterion puts `B i j` in the
   maximal ideal. Neither step cancels any tuple entry.
3. In the Leibniz formula (def-weil-pbc-matrix-determinant), each nonidentity
   permutation term has an off-diagonal factor in the maximal ideal. The diagonal
   product is congruent to one, since each diagonal entry is. Thus `B.det - 1` lies
   in the maximal ideal, and the unit criterion makes `B.det` a unit. For `n = 0`
   the empty product is one.
4. Choose an inverse `d` of the determinant and take `V = d • B.adjugate`.
   The two adjugate identities (lem-weil-pbc-matrix-adjugate-identity) and
   distributivity give both inverse equations, including for the empty matrix.
-/
theorem irredundant_relation_matrix {R : Type u} [CommRing R] [IsLocalRing R]
    (n : ℕ) (a : Fin n → R)
    (hirr : ∀ j : Fin n, ¬ ∃ c : Fin n → R,
      a j = ∑ i ∈ Finset.univ.erase j, a i * c i)
    (B : Matrix (Fin n) (Fin n) R)
    (hrel : ∀ j : Fin n, a j = ∑ i : Fin n, a i * B i j) :
    (∀ j : Fin n, 1 - B j j ∈ maximalIdeal R ∧ IsUnit (B j j)) ∧
      (∀ i j : Fin n, i ≠ j → B i j ∈ maximalIdeal R) ∧
      IsUnit B.det ∧
      ∃ V : Matrix (Fin n) (Fin n) R, B * V = 1 ∧ V * B = 1 := by
  sorry

end IsLocalRing
