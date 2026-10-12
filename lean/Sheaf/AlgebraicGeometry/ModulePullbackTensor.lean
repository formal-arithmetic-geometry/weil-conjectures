/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
import Sheaf.Algebra.Category.ModuleCat.Sheaf.StalkTensor
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Sheaf.AlgebraicGeometry.Modules.TensorPullbackStalk
import Sheaf.AlgebraicGeometry.TensorPullback

/-!
# Pullback of modules and tensor products

Source: Stacks Project, Modules, Lemma 17.16.4 (Tag 01CD), label
`lemma-tensor-product-pullback` (blueprint: lem-weil-pbc-module-pullback-tensor).

## Main statement

The tensor-formula pullback commutes naturally with tensor products and carries pure tensor
sections to pure tensor sections, as in the source statement.
-/

@[expose] public section

universe v

open CategoryTheory MonoidalCategory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false

/-- Pullback of modules commutes with tensor products, naturally and on sections. The pullback
`f^*u` of a section `u` over `V` is the component over `f ⁻¹ᵁ V` of the unit of the chosen
adjunction `Classical.choose (exists_tensorPullbackAdjunction f)`.

Source: Stacks Project, Modules, Lemma 17.16.4 (Tag 01CD), label
`lemma-tensor-product-pullback` (blueprint: lem-weil-pbc-module-pullback-tensor).
Proof: construct the comparison by adjunction from the bilinear map on sections; check its
stalks using the stalk pullback and tensor lemmas and the base-change tensor identity; detect
isomorphisms on stalks. Naturality follows from the same adjunction and the sheaf tensor
universal property.
-/
theorem module_pullback_tensor {X Y : Scheme.{v}} (f : X ⟶ Y) :
    ∃ e : ∀ (M N : Y.Modules),
        (tensorPullback f).obj (M ⊗ N) ≅
          (tensorPullback f).obj M ⊗ (tensorPullback f).obj N,
      (∀ (M N M' N' : Y.Modules) (a : M ⟶ M') (b : N ⟶ N'),
        (tensorPullback f).map (a ⊗ₘ b) ≫ (e M' N').hom =
          (e M N).hom ≫ ((tensorPullback f).map a ⊗ₘ (tensorPullback f).map b)) ∧
      (∀ (M N : Y.Modules) (V : Y.Opens) (s : Γ(M, V)) (t : Γ(N, V)),
        (e M N).hom.app (f ⁻¹ᵁ V)
            (((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app (M ⊗ N)).val.app
              (op V) (tmulSection s t) : Γ((tensorPullback f).obj (M ⊗ N), f ⁻¹ᵁ V)) =
          tmulSection
            (((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app M).val.app
              (op V) s : Γ((tensorPullback f).obj M, f ⁻¹ᵁ V))
            (((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app N).val.app
              (op V) t : Γ((tensorPullback f).obj N, f ⁻¹ᵁ V))) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
