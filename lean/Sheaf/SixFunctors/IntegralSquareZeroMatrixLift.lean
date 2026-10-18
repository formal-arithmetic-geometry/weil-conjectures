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
  sorry
