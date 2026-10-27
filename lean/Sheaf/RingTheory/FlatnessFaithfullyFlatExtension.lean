/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q44
-/
module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs

/-!
# Flatness over a base after a faithfully flat intermediate extension

Source: Stacks Project, Algebra, Tag 0584, part (2),
`lemma-flatness-descends-more-general`.
(blueprint: lem-trf-flatness-faithfully-flat-extension)
-/

@[expose] public section

universe u v w t

open scoped TensorProduct

namespace Module.Flat

/-- Flatness over `A` is preserved and reflected by a faithfully flat extension `B → C`.
The scalar towers specify the induced `A`-actions on `N` and `C ⊗[B] N`.
Source: Stacks Project, Algebra, Tag 0584, part (2).
(blueprint: lem-trf-flatness-faithfully-flat-extension)

Proof:
1. By faithful flatness (`def-weil-pbc-faithfully-flat-ring-map`), tensoring a
   `B`-linear map with `C` preserves and reflects injectivity: apply preservation
   and reflection of exactness to the complex `0 → P → Q`. The tensor product
   with zero is zero by `def-weil-pbc-module-tensor-product`.
2. For each `A`-module `U`, the tensor universal property
   (`def-weil-pbc-module-tensor-product`) gives the `A`-linear isomorphism
   `C ⊗[B] (U ⊗[A] N) ≃ U ⊗[A] (C ⊗[B] N)` sending
   `c ⊗ (u ⊗ n)` to `u ⊗ (c ⊗ n)`. Its reverse formula respects the same
   balancing relations, and both composites fix pure tensors. For an `A`-linear
   map `f : U → V`, this isomorphism intertwines `1_C ⊗ (f ⊗ 1_N)` with
   `f ⊗ 1_(C ⊗ N)`, since both send that generator to `f(u) ⊗ (c ⊗ n)`.
3. If `N` is flat over `A`, then `f ⊗ 1_N` is injective for every injective
   `A`-linear `f` (`def-weil-pbc-flat-ring-map`). This map is `B`-linear.
   Step 1 preserves its injectivity, and Step 2 transports it to injectivity
   of `f ⊗ 1_(C ⊗ N)`. Thus `C ⊗[B] N` is flat over `A`.
4. Conversely, if `C ⊗[B] N` is flat over `A`, Step 2 identifies the tensor
   with `C` of `f ⊗ 1_N` with an injective map for every injective `f`.
   Step 1 reflects injectivity, so `f ⊗ 1_N` is injective. The flatness
   criterion `def-weil-pbc-flat-ring-map` proves that `N` is flat over `A`. -/
theorem iff_flat_tensorProduct_of_faithfullyFlat_extension
    {A : Type u} {B : Type v} {C : Type w} {N : Type t}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
    [Module.FaithfullyFlat B C] :
    Module.Flat A N ↔ Module.Flat A (C ⊗[B] N) := by
  have tensor_injective_iff
      {P Q : Type (max u w t)} [AddCommGroup P] [AddCommGroup Q]
      [Module A P] [Module A Q] (f : P →ₗ[A] Q) :
      Function.Injective (f.lTensor (C ⊗[B] N)) ↔
        Function.Injective (f.lTensor N) := by
    let g := TensorProduct.AlgebraTensorModule.lTensor B N f
    have h : g.lTensor C =
        (TensorProduct.AlgebraTensorModule.assoc A B B C N Q).toLinearMap ∘ₗ
          TensorProduct.AlgebraTensorModule.lTensor B (C ⊗[B] N) f ∘ₗ
          (TensorProduct.AlgebraTensorModule.assoc A B B C N P).symm.toLinearMap := by
      ext c n p
      rfl
    have hi := Module.FaithfullyFlat.lTensor_injective_iff_injective B C g
    rw [h] at hi
    simpa only [g, LinearMap.coe_comp, LinearEquiv.coe_coe,
      EquivLike.injective_comp, EquivLike.comp_injective,
      TensorProduct.AlgebraTensorModule.coe_lTensor] using hi
  constructor
  · intro h
    let := h
    refine Module.Flat.iff_lTensor_preserves_injective_linearMap'.mpr
      (fun {P Q : Type (max u w t)} _ _ _ _ f hf ↦ ?_)
    exact (tensor_injective_iff f).mpr (lTensor_preserves_injective_linearMap f hf)
  · intro h
    let := h
    refine Module.Flat.iff_lTensor_preserves_injective_linearMap'.mpr
      (fun {P Q : Type (max u w t)} _ _ _ _ f hf ↦ ?_)
    exact (tensor_injective_iff f).mp (lTensor_preserves_injective_linearMap f hf)

end Module.Flat
