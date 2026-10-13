/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
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
1. Choose a primitive element alpha (`lem-weil-pbc-finite-separable-extension-primitive-element`).
   Its minimal polynomial P is monic, irreducible and separable
   (`def-weil-pbc-separable-algebraic-extension`, `def-weil-polynomial-ring`,
   `def-pc-separable-polynomial`). The power basis
   (`lem-weil-pbc-simple-algebraic-extension-power-basis`) identifies K with L[T]/(P).
2. Swap tensor factors and extend scalars in this presentation. Polynomial scalar extension
   (`lem-weil-pbc-polynomial-scalar-extension`, `def-weil-polynomial-ring`) and quotient base
   change (`lem-weil-pbc-tensor-quotient-base-change`) identify K tensor E with E[T]/(P bar).
3. Extend the coefficients of a Bezout identity for P and its derivative to E. Coefficient
   extension commutes with the derivative, so P bar is separable
   (`def-pc-separable-polynomial`).
4. The quotient by P bar is reduced (`lem-weil-pbc-separable-polynomial-quotient-reduced`).
   Transport reducedness through the ring isomorphism from step 2: it maps nilpotents to
   nilpotents and is injective. -/
theorem isReduced_tensorProduct_of_finiteSeparable
    (L : Type u) (K : Type v) (E : Type w)
    [Field L] [Field K] [Field E] [Algebra L K] [Algebra L E]
    [FiniteDimensional L K] [Algebra.IsSeparable L K] : IsReduced (K ⊗[L] E) := by
  have : FormallyUnramified L K := .of_isSeparable L K
  have : EssFiniteType E (E ⊗[L] K) := .of_finiteType _ _
  have := FormallyUnramified.isReduced_of_field E (E ⊗[L] K)
  exact isReduced_of_injective (Algebra.TensorProduct.comm L K E).toRingHom
    (Algebra.TensorProduct.comm L K E).injective

end Algebra
