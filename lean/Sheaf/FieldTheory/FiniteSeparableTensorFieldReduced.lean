/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.RingTheory.Unramified.Field

/-!
# Reducedness of a finite separable extension tensored with a field

Source: Stacks Project, Algebra, Tag 030U, first paragraph of the proof, with
Fields, Tag 030N (primitive element theorem).
(blueprint: lem-weil-pbc-finite-separable-tensor-field-reduced).
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Algebra

/-- If `K/L` is finite separable algebraic and `E/L` is any field extension, the ring
`K ⊗[L] E` has no nonzero nilpotent elements. Its multiplication and unit are the
standard tensor-product ring operations.
Source: Stacks Project, Algebra, Tag 030U, first paragraph of the proof; Fields, Tag 030N.
(blueprint: lem-weil-pbc-finite-separable-tensor-field-reduced).

Proof:
A separable field extension is formally unramified
(`Algebra.FormallyUnramified.of_isSeparable`). Base change makes `E ⊗[L] K` formally
unramified over `E`. Finiteness of `K/L` makes this tensor product finite type over `E`,
so `Algebra.FormallyUnramified.isReduced_of_field` shows that it is reduced.
Transport reducedness along the tensor commutativity isomorphism. -/
theorem isReduced_tensorProduct_of_finiteSeparable
    (L : Type u) (K : Type v) (E : Type w)
    [Field L] [Field K] [Field E] [Algebra L K] [Algebra L E]
    [FiniteDimensional L K] [Algebra.IsSeparable L K] : IsReduced (K ⊗[L] E) := by
  have : FormallyUnramified L K := FormallyUnramified.of_isSeparable L K
  have : IsReduced (E ⊗[L] K) := FormallyUnramified.isReduced_of_field E _
  exact isReduced_of_injective (TensorProduct.comm L K E) (AlgEquiv.injective _)

end Algebra
