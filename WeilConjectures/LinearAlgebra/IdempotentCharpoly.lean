/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# A determinant formula for the characteristic polynomial on an idempotent summand

For a matrix `T` and an idempotent `P` commuting with it, `idempotentCharpoly T P` is the
determinant of `1 - P + (X - T) P`, the characteristic polynomial of `T` on the image of `P`.

## References

* [Stacks Project, Tag 09XI](https://stacks.math.columbia.edu/tag/09XI)
-/

@[expose] public section

universe u v

namespace Matrix

variable {A : Type u} [CommRing A] {n : Type v} [Fintype n] [DecidableEq n]

/-- The determinant of `1-P + (X-T)P`. If P is an idempotent commuting with T,
this is the characteristic polynomial of T on the image of P: on the complementary
summand the matrix is the identity. This formula uses only the ambient free module. -/
noncomputable def idempotentCharpoly (T P : Matrix n n A) : Polynomial A :=
  (1 - Polynomial.C.mapMatrix P + T.charmatrix * Polynomial.C.mapMatrix P).det

end Matrix
