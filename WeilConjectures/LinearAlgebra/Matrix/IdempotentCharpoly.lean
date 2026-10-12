/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# The idempotent characteristic polynomial

For square matrices `T, P` over a commutative ring `A`, `D(T, P) = det(1 - C(P) + (X - C(T)) C(P))`.
When `P` is an idempotent commuting with `T`, this is the characteristic polynomial of `T`
restricted to the image of `P`.
-/

@[expose] public section

namespace Matrix

variable {J : Type*} [Fintype J] [DecidableEq J] {A : Type*} [CommRing A]

/-- `D(T, P) = det(1 - C(P) + (X·1 - C(T))·C(P)) ∈ A[X]`, with `C` the constant-polynomial map
applied entrywise; `X·1 - C(T)` is `Matrix.charmatrix T`. No hypothesis on `T, P` is imposed.
(blueprint: `def-weil-pbc-idempotent-charpoly`) -/
noncomputable def idempotentCharpoly (T P : Matrix J J A) : Polynomial A :=
  (1 - P.map Polynomial.C + charmatrix T * P.map Polynomial.C).det

end Matrix
