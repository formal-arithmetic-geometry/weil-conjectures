/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.MatrixAlgebra
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Automorphisms of matrix algebras are inner

The **Skolem–Noether theorem** for matrix algebras over a field: every `F`-algebra automorphism
of `Matrix n n F` is conjugation by an invertible matrix. In particular it preserves the
determinant.

## Main statements

- `Matrix.exists_unit_conj_of_algEquiv`: an automorphism of `Matrix n n F` is inner.
- `Matrix.det_algEquiv_apply`: an automorphism of `Matrix n n F` preserves the determinant.
-/

@[expose] public section

namespace Matrix

variable {F n : Type*} [Field F] [Fintype n] [DecidableEq n]

/-- **Skolem–Noether for matrix algebras.** Every `F`-algebra automorphism of `Matrix n n F`
is conjugation by a unit: with `v` a nonzero vector in the image of `σ (single i₀ i₀ 1)`, the
matrix with columns `σ (single j i₀ 1) v` intertwines the identity and `σ`. -/
@[stacks 074P]
theorem exists_unit_conj_of_algEquiv (σ : Matrix n n F ≃ₐ[F] Matrix n n F) :
    ∃ g : (Matrix n n F)ˣ, ∀ X, σ X = g * X * g⁻¹ :=
  sorry

/-- An `F`-algebra automorphism of `Matrix n n F` preserves the determinant. -/
theorem det_algEquiv_apply (σ : Matrix n n F ≃ₐ[F] Matrix n n F) (X : Matrix n n F) :
    (σ X).det = X.det :=
  sorry

end Matrix
