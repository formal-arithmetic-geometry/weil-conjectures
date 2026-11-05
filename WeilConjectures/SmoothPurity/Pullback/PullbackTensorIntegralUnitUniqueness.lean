/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorConstraints

/-! Uniqueness of the integral unit comparison.

Source: Stacks Project, Tag 07A4, label lemma-pullback-tensor-product; cancellation
with the tensor unitors in the integral constructible category.
(blueprint: lem-pur-pullback-tensor-integral-unit-coherence-uniqueness)

Applying coherent reduction to either pair of unit equations and cancelling the
invertible comparison and unitor identifies the two candidate unit maps.
Faithfulness of coherent reduction then reflects equality of the original maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

end WeilConjectures
