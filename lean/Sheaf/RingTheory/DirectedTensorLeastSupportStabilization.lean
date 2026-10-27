/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q53
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.Order.Bounds.Defs
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-!
# Stabilization of least tensor supports in a directed colimit

Source: Stacks Project, Algebra, Tag 059S (lemma-flat-ML-criterion), the commutative
square and final paragraph of its proof, formulated using tensor images.
(blueprint: lem-trf-directed-tensor-least-support-stabilization).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace Module

/-- Least supports decrease along a directed module system and eventually equal the least
support in its colimit. Supporting a tensor means belonging to the image of the tensor
of a submodule inclusion; tensor inclusions need not be injective.

Source: Stacks Project, Algebra, Tag 059S (lemma-flat-ML-criterion), proof, commutative
square and final paragraph beginning "Since the Q_j are decreasing".
(blueprint: lem-trf-directed-tensor-least-support-stabilization).

Proof:
1. For a submodule `G` of `H` and a linear map `f : L →ₗ[R] L'`, the square formed by
   the two tensor inclusion maps and `1 ⊗ f` commutes, as checked on pure tensors
   (def-weil-pbc-module-tensor-product). Thus a support remains a support after applying
   `1 ⊗ f`. Leastness gives `Q ≤ C k hk` and decreasingness of the stage supports.
2. Tensoring the colimit with any fixed module preserves its colimit, first using
   lem-weil-pbc-tensor-commutes-with-colimits and then tensor symmetry to put that module
   on the left. Since `Q` supports the colimit tensor, choose its lift in `Q ⊗ N`.
   By lem-weil-pbc-filtered-colimit-modules-elementwise (representatives), lift this
   further to `Q ⊗ N_h` for some stage `h`.
3. Its image in `H ⊗ N_h` and the given tensor at `i` have equal colimit images.
   By lem-weil-pbc-filtered-colimit-modules-elementwise (eventual equality), they agree
   at a common later stage `j ≥ h, i`. Transporting the lift to `Q ⊗ N_j` gives `t`;
   the square of step 1 identifies its image with the specified tensor at `j`.
4. This witness shows that `Q` supports the tensor at `j`, so leastness gives
   `C j hj ≤ Q`. Together with step 1 this gives equality. For any `k ≥ j`, step 1
   gives `Q ≤ C k (hj.trans hk) ≤ C j hj = Q`, proving stabilization.
-/
theorem directed_tensor_least_support_stabilization
    {R : Type u} [CommRing R] {H : Type w} [AddCommGroup H] [Module R H]
    {I : Type v} [PartialOrder I] [Nonempty I] [IsDirectedOrder I]
    (F : I ⥤ ModuleCat.{v} R) (c : Cocone F) (hc : IsColimit c)
    (i : I) (xi : TensorProduct R H (F.obj i)) (Q : Submodule R H)
    (C : ∀ k : I, i ≤ k → Submodule R H)
    (hQ : IsLeast
      {G : Submodule R H |
        LinearMap.lTensor H (c.ι.app i).hom xi ∈
          LinearMap.range (LinearMap.rTensor c.pt G.subtype)} Q)
    (hC : ∀ (k : I) (hk : i ≤ k), IsLeast
      {G : Submodule R H |
        LinearMap.lTensor H (F.map (homOfLE hk)).hom xi ∈
          LinearMap.range (LinearMap.rTensor (F.obj k) G.subtype)} (C k hk)) :
    (∀ (k : I) (hk : i ≤ k), Q ≤ C k hk) ∧
      (∀ (k l : I) (hk : i ≤ k) (hkl : k ≤ l), C l (hk.trans hkl) ≤ C k hk) ∧
      ∃ (j : I) (hj : i ≤ j) (t : TensorProduct R Q (F.obj j)),
        LinearMap.rTensor (F.obj j) Q.subtype t =
          LinearMap.lTensor H (F.map (homOfLE hj)).hom xi ∧
        ∀ (k : I) (hk : j ≤ k), C k (hj.trans hk) = Q := by
  sorry

end Module
