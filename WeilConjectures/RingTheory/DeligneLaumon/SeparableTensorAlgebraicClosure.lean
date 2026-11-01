/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import WeilConjectures.FieldTheory.SeparableExtension
public import WeilConjectures.FieldTheory.Picard.FieldTower
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.Algebra.Algebra.Pi

/-!
# A finite separable field tensored with an algebraically closed field

Source: Stacks Project, Tag 0FD1, proof, residue-field base change; Tags 030U, 00U3,
030N, and 09GU for the polynomial presentation and splitting argument
(blueprint: lem-pc-separable-tensor-algebraic-closure).
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Algebra

attribute [local instance] TensorProduct.rightAlgebra

end Algebra
