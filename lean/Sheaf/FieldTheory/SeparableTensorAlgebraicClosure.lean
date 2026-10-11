/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Sheaf.FieldTheory.SeparableExtension
import Sheaf.FieldTheory.FieldTower

/-!
# A finite separable field tensored with an algebraically closed field

Source: Stacks Project, Tag 0FD1, proof, residue-field base change; Tags 030U, 00U3,
030N, and 09GU for the polynomial presentation and splitting argument
(blueprint: lem-pc-separable-tensor-algebraic-closure).
-/

universe u v w

open scoped TensorProduct

namespace Algebra

attribute [local instance] TensorProduct.rightAlgebra

/-- A finite separable extension tensored with an algebraically closed field is a product
of copies of that field indexed by the base-field embeddings. The number of factors is
the extension degree.
Source: Stacks Project, Tag 0FD1, proof, with Tags 030U, 00U3, 030N, and 09GU.
(blueprint: lem-pc-separable-tensor-algebraic-closure).

Proof: (1) Finite-dimensionality makes every element algebraic
(`def-weil-algebraic-element`), so a transcendence basis is empty
(`def-weil-pbc-transcendence-basis`). Applying `IsSeparableExtension` to the whole
finitely generated extension gives separable algebraicity
(`def-weil-pbc-separable-algebraic-extension`). Choose a primitive element
(`lem-weil-pbc-finite-separable-extension-primitive-element`), with monic separable
minimal polynomial P; its power basis gives K = k[T]/(P)
(`lem-weil-pbc-simple-algebraic-extension-power-basis`).
(2) Base change gives Omega[T]/(P bar), using
`lem-weil-pbc-polynomial-scalar-extension` and `lem-weil-pbc-tensor-quotient-base-change`.
(3) A Bezout identity for P and its derivative survives coefficient extension
(`def-pc-separable-polynomial`). The Chinese remainder decomposition is a product
of Omega indexed by roots (`lem-pc-separable-polynomial-alg-closed-quotient-product`).
(4) Evaluation at a root corresponds uniquely to a k-embedding of K into Omega.
The number of roots is the degree of P, hence [K:k], by the power basis or
`lem-pc-finrank-field-base-change`. Reindexing by `Fin n` yields n copies of Omega.
The tensor product carries the Omega-algebra structure on its right factor. -/
theorem separable_tensor_algebraicallyClosed_equiv_pi
    (k : Type u) (K : Type v) (Ω : Type w)
    [Field k] [Field K] [Field Ω] [Algebra k K] [Algebra k Ω]
    [FiniteDimensional k K] [IsAlgClosed Ω]
    (hsep : Algebra.IsSeparableExtension k K) :
    Nonempty ((K ⊗[k] Ω) ≃ₐ[Ω] ((K →ₐ[k] Ω) → Ω)) ∧
      ∃ n : ℕ, FieldExtension.degree k K = (n : WithTop ℕ) ∧
        Nonempty ((K →ₐ[k] Ω) ≃ Fin n) := by
  sorry

end Algebra
