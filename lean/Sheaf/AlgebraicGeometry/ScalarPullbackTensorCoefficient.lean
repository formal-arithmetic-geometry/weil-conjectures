/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations

/-! # ScalarPullbackTensorCoefficient

Source: Stacks Project, Cohomology, Tags 01F7, 01FD, 07MB and 0FKV.
-/

@[expose] public section

universe w
set_option autoImplicit false
open CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Sheaf.monoidalCategory HasExt.standard
variable {k : Type w} [Field k] {X Y : Scheme.{w}}

/-- The scalar tensor coefficient commutes with the normalized module pullback
comparison. This is an equality of coefficient sheaf morphisms, with no Ext classes.
Source: Stacks Project, Cohomology, Tag 01F7; Modules, Tag 01CD.
(blueprint: lem-sc-scalar-pullback-tensor-coefficient).

Proof: Apply the inverse-image/direct-image adjunction to the two morphisms.
Precompose their underlying presheaf morphisms with the tensorator of the sheaf
inclusion. Evaluate over each open U on a pure tensor s tensor r. The defining
adjunction identity for scalarPullbackCoefficient identifies each factor with the
normalized module pullback unit applied to s or r. The section formula for
scalarTensorCoefficient sends a pure tensor to tmulSection s r. The section
normalization of module_pullback_tensor sends the unit applied to this tensor
section to the tensor of the two unit sections. The oplax comparison is the mate
of the lax tensor comparison for direct image, so its adjoint gives precisely the
same tensor of unit sections. Thus both composites agree on pure tensors. The
linear tensor universal property extends the equality to presheaf tensors, and
the sheafification adjunction extends it to the sheaf tensor. Finally injectivity
of the inverse-image adjunction gives the displayed coefficient square. Empty
schemes and zero modules require no exception: all these section identities hold.
-/
theorem scalarPullbackCoefficient_tensor
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (t : Y ⟶ X) (ht : t ≫ f = g) (F G : X.Modules) :
    (scalarInverseImage t).map (scalarTensorCoefficient f F G) ≫
        scalarPullbackCoefficient f g t ht (@id X.Modules (F ⊗ G)) ≫
        scalarHom g ((Classical.choose (module_pullback_tensor t)) F G).hom =
      ((Opens.map t.base).sheafAdjunctionContinuous (ModuleCat.{w} k)
        (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).leftAdjointOplaxMonoidal.δ
          (scalarSheaf f F) (scalarSheaf f G) ≫
        (scalarPullbackCoefficient f g t ht F ⊗ₘ
          scalarPullbackCoefficient f g t ht G) ≫
        scalarTensorCoefficient g ((tensorPullback t).obj F)
          ((tensorPullback t).obj G) := by sorry

end
end AlgebraicGeometry.Scheme.Modules
