module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.TwoSidedIdeal.Basic
public import Mathlib.RingTheory.Congruence.Defs

set_option autoImplicit false

@[expose] public section

universe u

/-! # Square-zero matrix lifts

Source: Bhatt--Scholze, Proposition 6.8.4(1), p. 59 (blueprint:
lem-sfb-integral-square-zero-matrix-lift).
-/

/--
Source: Bhatt--Scholze, Proposition 6.8.4(1), p. 59; the source leaves this
square-zero matrix calculation to the reader.  The proof follows the four
steps in the node: lift the inverse entrywise, establish that the two errors
lie in the square-zero ideal and square to zero, compute right and left
inverses by the correction factors, and identify those corrections.
(blueprint: lem-sfb-integral-square-zero-matrix-lift)
-/
theorem integral_square_zero_matrix_lift
    (R : Type u) [Ring R] (I : TwoSidedIdeal R)
    (hI : ∀ x y : R, x ∈ I → y ∈ I → x * y = 0)
    (r : ℕ) (B : Matrix (Fin r) (Fin r) R)
    (D : Matrix (Fin r) (Fin r) I.ringCon.Quotient)
    (hBD : B.map I.ringCon.mk' * D = 1)
    (hDB : D * B.map I.ringCon.mk' = 1)
    (C : Matrix (Fin r) (Fin r) R)
    (hC : ∀ i j, I.ringCon.mk' (C i j) = D i j) :
    let N : Matrix (Fin r) (Fin r) R := B * C - 1
    let P : Matrix (Fin r) (Fin r) R := C * B - 1
    B * (C * (1 - N)) = 1 ∧
      (1 - P) * C * B = 1 ∧
      C * (1 - N) = (1 - P) * C := by
  let N : Matrix (Fin r) (Fin r) R := B * C - 1
  let P : Matrix (Fin r) (Fin r) R := C * B - 1
  have hmapC : C.map I.ringCon.mk' = D := by
    ext i j
    exact hC i j
  have hmapN : N.map I.ringCon.mk' = 0 := by
    change I.ringCon.mk'.mapMatrix (B * C - 1) = 0
    rw [map_sub, map_mul, map_one]
    change B.map I.ringCon.mk' * C.map I.ringCon.mk' - 1 = 0
    rw [hmapC, hBD, sub_self]
  have hmapP : P.map I.ringCon.mk' = 0 := by
    change I.ringCon.mk'.mapMatrix (C * B - 1) = 0
    rw [map_sub, map_mul, map_one]
    change C.map I.ringCon.mk' * B.map I.ringCon.mk' - 1 = 0
    rw [hmapC, hDB, sub_self]
  have hsquare (M : Matrix (Fin r) (Fin r) R)
      (hM : M.map I.ringCon.mk' = 0) : M * M = 0 := by
    have hmem (i j : Fin r) : M i j ∈ I := by
      apply (I.mem_iff _).mpr
      apply I.ringCon.eq.mp
      change I.ringCon.mk' (M i j) = I.ringCon.mk' 0
      rw [map_zero]
      exact congrFun (congrFun hM i) j
    ext i j
    change ∑ k, M i k * M k j = 0
    apply Finset.sum_eq_zero
    intro k _
    exact hI _ _ (hmem i k) (hmem k j)
  have hN : N * N = 0 := hsquare N hmapN
  have hP : P * P = 0 := hsquare P hmapP
  have hBC : B * C = 1 + N := by dsimp [N]; abel
  have hCB : C * B = 1 + P := by dsimp [P]; abel
  change B * (C * (1 - N)) = 1 ∧ (1 - P) * C * B = 1 ∧
    C * (1 - N) = (1 - P) * C
  refine ⟨?_, ?_, ?_⟩
  · rw [← mul_assoc, hBC]
    simp only [add_mul, mul_sub, one_mul, mul_one, hN]
    abel
  · rw [mul_assoc, hCB]
    simp only [mul_add, sub_mul, mul_one, one_mul, hP]
    abel
  · dsimp [N, P]
    simp only [mul_sub, sub_mul, mul_one, one_mul, mul_assoc]
