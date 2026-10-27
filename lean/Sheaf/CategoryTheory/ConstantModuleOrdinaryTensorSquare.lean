/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y3
-/
module

public import Sheaf.CategoryTheory.ConstantModuleGeometricComparisonData

/-! # Ordinary tensor compatibility of the constant-module mate

Source: Stacks Project, Cohomology on Sites, Tag 07A4, and Modules on Sites, Tag 03EL.
(blueprint: lem-sfb-constant-module-ordinary-tensor-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

attribute [local irreducible] SheafOfModules.monoidalCategory
  SheafOfModules.symmetricCategory CategoryTheory.ConstantScalarRestriction.fixedMonoidal
  CategoryTheory.ConstantScalarRestriction.fixedSymmetric
  CategoryTheory.ConstantScalarRestriction.restrictionBraided
  CategoryTheory.ConstantScalarRestriction.ordinary
attribute [-instance] CategoryTheory.ConstantScalarRestriction.ringPreadditive
  CategoryTheory.ConstantScalarRestriction.fixedPreadditive
  CategoryTheory.ConstantScalarRestriction.ringZeroMorphisms
  CategoryTheory.ConstantScalarRestriction.fixedZeroMorphisms
universe u v
open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.ConstantScalarRestriction
namespace CategoryTheory.ConstantModuleDerivedProjection

/-- The mate-normalized ordinary comparison preserves the specified tensor comparisons.
Source: Stacks Tags 07A4 and 03EL; step 1 of
`lem-sfb-constant-module-tensor-square-descent`.
(blueprint: lem-sfb-constant-module-ordinary-tensor-square).

Proof: the Hom equation for `o.left`, the underlying equation for `o.right`, and the
ringed Hom equation identify the underlying inverse-image map of `o.left` with the
scalar-extension insertion `1 tensor x`. The Hom equation for `t.underlying` identifies
its inverse with the same geometric adjunction mate. Apply `d.ringTensor.pure` and
`t.pure` to the generalized elements of the product of the underlying sheaves of two
modules. The two scalar-restriction tensorators retain the same pure tensors by
`ordinary.tensor_hom`. Thus both routes in the displayed square agree on every such
inverse-image pure tensor. Finite-limit preservation of the geometric inverse image
identifies pairs of generalized sections with sections of the inverse image of that
product. The tensor universal property, scalar-extension balancing, and the
sheafification adjunction show that these sections determine the two maps. Hence the
maps agree on all module sheaves. This argument uses only ordinary sheaves and does
not assert any derived normalization or make any choice of a derived monoidal structure.
The zero ring and empty sites require no separate argument: the same universal
properties apply there. -/
theorem constant_module_ordinary_tensor_square
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {A : Type (max u v)} [CommRing A]
    (d : GeometricData J K A) (o : OrdinaryIdentification d) (t : FixedTensorData d)
    (m : d.pullR.Monoidal)
    (hm : ∀ M N, @Functor.OplaxMonoidal.δ _ _ _ _ _ _ d.pullR
      m.toOplaxMonoidal M N = (d.ringTensor.mu M N).hom) :
    TensorSquare d.pullR d.pullA (restriction J A) (restriction K A)
      m t.monoidal (restrictionBraided J A).toMonoidal
        (restrictionBraided K A).toMonoidal o.left := by sorry

end CategoryTheory.ConstantModuleDerivedProjection
