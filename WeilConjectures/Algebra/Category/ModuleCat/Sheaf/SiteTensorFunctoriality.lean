/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.Algebra.Homology.Additive

/-!
# Zero morphisms and the general-site tensor product

Source: Stacks Project, Modules on Sites, Section 03EK
(blueprint: def-pur-sheaf-tensor-product).
The existing independent-universe tensor product is retained. This module shows that tensoring
with a fixed right factor preserves zero morphisms.
-/

@[expose] public section

universe uC vC r m

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasWeakSheafify J AddCommGrpCat.{m}]
  {A : Sheaf J CommRingCat.{r}}

/-- Tensor with a fixed right factor preserves zero morphisms.
Source: Stacks, Section 03EK (blueprint: def-pur-sheaf-tensor-product).
Proof: sectionwise, `0 ⊗ id` vanishes on pure tensors, hence is the zero linear map.
The forgetful functor and additive module sheafification preserve zero maps as well. -/
theorem siteSheafTensorRight_preservesZeroMorphisms
    (N : SheafOfModules.{m} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)) :
    (siteSheafTensorRight N).PreservesZeroMorphisms := by
  have : (siteTensorRight N.val).PreservesZeroMorphisms := by
    refine ⟨?_⟩
    intro M M'
    ext U : 1
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x y
    change (0 : M.obj U →ₗ[A.obj.obj U] M'.obj U) x ⊗ₜ[A.obj.obj U] y = 0
    simp
  dsimp only [siteSheafTensorRight]
  infer_instance

attribute [instance] siteSheafTensorRight_preservesZeroMorphisms

end SheafOfModules
