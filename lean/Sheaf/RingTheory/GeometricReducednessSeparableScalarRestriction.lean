/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Nilpotent.Defs
import WeilConjectures.FieldTheory.SeparablyGeneratedTensorReduced
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Geometric reducedness and separable algebraic restriction of scalars

Source: Stacks Project, Algebra, Tag 0C2Y,
`lemma-geometrically-reduced-over-separable-algebraic`
(blueprint: lem-trf-geometric-reducedness-separable-scalar-restriction).

We use the all-extension-fields formulation of geometric reducedness, with the field
in the left tensor factor. The universe `t` is independent of the universes of `k`,
`k₁`, and `A`; both tests take place in their common enlarged universe.
-/

@[expose] public section

universe u v w t

open scoped TensorProduct

namespace Algebra

/-- Restricting scalars along a separable algebraic field extension preserves and reflects
geometric reducedness, without finite-generation, finite-degree, or nonzero assumptions on
`A`. The scalar tower says that its `k`-algebra structure is the restricted one. Tensor
products have their usual commutative ring structures, and `IsReduced` says every nilpotent
is zero. Source: Stacks Project, Algebra, Tag 0C2Y
(blueprint: lem-trf-geometric-reducedness-separable-scalar-restriction).

Proof, following the two steps of the node:
1. Assume the right side and take a field extension `E/k`. The empty transcendence basis
   makes `k₁/k` separably generated (`def-weil-pbc-separable-field-extension`,
   `def-weil-pbc-transcendence-basis`, `def-weil-pbc-separable-algebraic-extension`).
   Apply `lem-weil-pbc-separably-generated-tensor-reduced` (030U) to `k₁` and `E`, and
   swap factors to see that `E ⊗[k] k₁` is reduced. Apply
   `lem-trf-geometrically-reduced-base-change` (034N) over `k₁` to this reduced algebra
   and `A`. The cancellation isomorphism of `lem-weil-pbc-tensor-cancel-base-change`,
   together with swaps, identifies the result with `E ⊗[k] A`: it sends
   `(e ⊗ b) ⊗ a` to `e ⊗ (b * a)` with inverse `e ⊗ a` to `(e ⊗ 1) ⊗ a`.
2. Assume the left side and take `E/k₁`. Restrict its scalars to `k`, so
   `D = E ⊗[k] A` is reduced. Put `R = k₁ ⊗[k] k₁`, acting on `D` by
   `(b ⊗ c) * (e ⊗ a) = (b * e) ⊗ (c * a)`, and on `k₁` by multiplication.
   The ring isomorphism `E ⊗[k₁] A ≃ D ⊗[R] k₁` sends `e ⊗ a` to
   `(e ⊗ a) ⊗ 1`; its inverse sends `(e ⊗ a) ⊗ c` to `(c * e) ⊗ a`.
   The first map is balanced since both actions of `b : k₁` become multiplication
   by `b` in the last factor; the inverse is `R`-balanced since the image of
   `b ⊗ c` in `E ⊗[k₁] A` acts by `b * c`. Both preserve products and units,
   and their composites are the identity on pure tensors, using
   `(e ⊗ a) ⊗ c = ((c * e) ⊗ a) ⊗ 1`. This is a direct balanced-map argument,
   not an application of the cancellation lemma in step 1.
   By `lem-trf-separable-algebraic-diagonal-localization` (0C2X), the multiplication
   `R → k₁` is a localization at some `S`. By `lem-weil-pbc-localization-base-change`,
   `D ⊗[R] k₁` is a localization of `D` at the image `T` of `S`.
   A localization of a reduced ring is reduced: for a nilpotent fraction `x/s`,
   take a positive exponent `n` with `x^n/s^n = 0`. Some `z ∈ T` satisfies
   `z * x^n = 0`, whence `(z * x)^n = z^(n-1) * (z * x^n) = 0`.
   Reducedness gives `z * x = 0`, hence `x/s = 0`. Transport across the isomorphism.
-/
theorem forall_isReduced_tensorProduct_iff_of_isSeparable
    (k : Type u) (k₁ : Type v) (A : Type w)
    [Field k] [Field k₁] [CommRing A]
    [Algebra k k₁] [Algebra k₁ A] [Algebra k A]
    [IsScalarTower k k₁ A] [Algebra.IsSeparable k k₁] :
    (∀ (E : Type (max u v w t)) [Field E] [Algebra k E], IsReduced (E ⊗[k] A)) ↔
      (∀ (E : Type (max u v w t)) [Field E] [Algebra k₁ E], IsReduced (E ⊗[k₁] A)) := by
  sorry

end Algebra
