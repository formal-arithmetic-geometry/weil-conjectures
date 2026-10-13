/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q2
-/
module

public import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations

/-! # ScalarTensorUnitCoefficient

Source: Stacks Project, Cohomology, Tag 0FKU.
(blueprint: lem-sc-scalar-tensor-unit-coefficient).
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {X : Scheme.{u}}
attribute [local instance] Sheaf.monoidalCategory HasExt.standard

local instance : MonoidalCategory (SheafOfModules.{u} X.ringCatSheaf) :=
  SheafOfModules.monoidalCategory X.sheaf

/-- Scalar tensor coefficients and the scalar unit respect both module unitors.
Source: Stacks Project, Modules, Tags 0096 and 01CA; Cohomology, Tag 0FKU.
(blueprint: lem-sc-scalar-tensor-unit-coefficient).

Proof: For the right identity, precompose with the tensorator of the inclusion
of scalar sheaves into scalar presheaves. The sheafification adjunction reduces
the equality to equality of presheaf morphisms. Evaluate on pure tensors at
an open: the constant scalar unit sends a scalar r to scalarMap f r, and the
explicit tensor coefficient sends s tensor t to tmulSection s t. The right
module unitor sends tmulSection s r to r times s. The scalar right unitor
has exactly the same action. Pure tensors generate each sectionwise tensor
product, so the presheaf maps are equal. For the left identity use r tensor s:
the left module unitor sends tmulSection r s to r times s, agreeing with the
scalar left unitor. Naturality of scalarMap and the constant-sheaf adjunction
identify the scalar unit on each open with this sectionwise scalar map.
The sheafification adjunction gives both asserted sheaf equalities. This
argument holds for arbitrary modules, including zero modules and empty X. -/
theorem scalarTensorCoefficient_unit
    (f : X ⟶ Spec (CommRingCat.of k)) (F : X.Modules) :
    ((scalarSheaf f F) ◁ scalarUnitMorphism f) ≫
        scalarTensorCoefficient f F (SheafOfModules.unit X.ringCatSheaf) ≫
        scalarHom f (ρ_ F).hom = (ρ_ (scalarSheaf f F)).hom ∧
    (scalarUnitMorphism f ▷ (scalarSheaf f F)) ≫
        scalarTensorCoefficient f (SheafOfModules.unit X.ringCatSheaf) F ≫
        scalarHom f (λ_ F).hom = (λ_ (scalarSheaf f F)).hom := by sorry

end
end AlgebraicGeometry.Scheme.Modules
