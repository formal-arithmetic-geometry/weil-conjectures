/-
Copyright (c) 2026 The Weil SHEAF project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Weil SHEAF project
-/
module

public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.Order.Directed
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-!
# Tail factorizations bound tensor kernels of colimit maps

Source: Stacks Project, Algebra, Tag 059E, proof of (3) implies (2), with the
factorization hypothesis restricted to a cofinal tail
(blueprint: lem-trf-tail-factorizations-tensor-kernel).
-/

@[expose] public section

universe u v w t

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

/-- Tail transition factorizations bound the tensor kernel of a colimit leg.
Source: Stacks Project, Algebra, Tag 059E, proof of (3) implies (2), tail-only version
(blueprint: lem-trf-tail-factorizations-tensor-kernel).

Proof: Fix `L`. By `lem-weil-pbc-tensor-commutes-with-colimits`, tensoring the given
colimit cocone with `L` gives a colimit whose legs are exactly the tensors of its legs.
For an element in the kernel of the `i`-th leg, the zero-detection clause of
`lem-weil-pbc-filtered-colimit-modules-elementwise` gives `k₀ ≥ i` at which its
image is zero. Directedness gives a common upper bound `k` of `k₀` and `j`.
Functoriality of the transition maps and of tensoring implies that its image at
`k` is still zero. Choose the assumed factorization `h : F.obj k →ₗ[R] F.obj j`.
By tensor functoriality (`def-weil-pbc-module-tensor-product`), its image under
`fᵢⱼ ⊗ id` is the image under `h ⊗ id` of zero, hence is zero. This proves the
kernel inclusion for arbitrary `L`; no finite presentation or Mittag-Leffler
condition is used. -/
theorem ker_rTensor_colimit_leg_le_of_tail_factorizations
    {R : Type u} [CommRing R] {I : Type w} [PartialOrder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] (F : I ⥤ ModuleCat.{v} R)
    (c : Cocone F) (hc : IsColimit c) (i j : I) (hij : i ≤ j)
    (hfactor : ∀ (k : I) (hjk : j ≤ k),
      ∃ h : F.obj k →ₗ[R] F.obj j,
        h.comp (F.map (homOfLE (hij.trans hjk))).hom = (F.map (homOfLE hij)).hom)
    (L : Type t) [AddCommGroup L] [Module R L] :
    LinearMap.ker (LinearMap.rTensor L (c.ι.app i).hom) ≤
      LinearMap.ker (LinearMap.rTensor L (F.map (homOfLE hij)).hom) := by
  sorry

end ModuleCat
