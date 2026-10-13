/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import Sheaf.AlgebraicGeometry.ScalarUnitCohomologyCoordinates
public import Sheaf.AlgebraicGeometry.TensorPullbackStructureSheaf
import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
import Sheaf.AlgebraicGeometry.ScalarCohomologyExtCoefficientNaturality

/-! # Structure-sheaf pullback preserves the degree-zero class of one

Source: Stacks Project, Cohomology, Tags 0FKU and 01F7.
(blueprint: lem-sc-scalar-unit-class-pullback).
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

/-- Pullback followed by the structure-sheaf coefficient map preserves the class of one.
Source: Stacks Project, Cohomology, Tag 01F7, and Modules, Tags 0096 and 01CA.
(blueprint: lem-sc-scalar-unit-class-pullback).

Proof: In degree zero the injective-resolution comparison is the usual identification
of derived global sections with sections. Evaluation at one identifies the image of
the augmented section one under scalarCohomologyExtEquiv with mk₀ of
scalarUnitMorphism. Inverse image preserves degree-zero Ext classes. Under the
inverse-image/direct-image adjunction, scalarPullbackCoefficient is characterized
by the tensor-pullback adjunction unit on sections. Compose with the adjoint map
tensorPullbackObjUnitToUnit: the tensor-pullback adjunction identity makes this the
structure-sheaf ring map. That ring map takes one to one. The constant-sheaf
adjunction, evaluated at the terminal open, now identifies the composite with the
scalar-unit morphism on the destination; scalarInverseUnitIso is precisely the
constant-unit identification in this adjunction. Naturality of the cohomology-to-Ext
comparison in the coefficient map converts this morphism equality to the displayed
cohomology equality. This also holds on the empty scheme, where all sections vanish. -/
theorem scalar_unit_class_pullback (k : Type u) [Field k]
    (X Y : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k))
    (g : Y ⟶ Spec (CommRingCat.of k)) (t : Y ⟶ X) (h : t ≫ f = g) :
    scalarCohomologyMap g (tensorPullbackObjUnitToUnit t) 0
      (scalarCohomologyPullback f g t h (SheafOfModules.unit X.ringCatSheaf) 0
        (scalarUnitCohomologyClass f)) = scalarUnitCohomologyClass g := by
  sorry

end AlgebraicGeometry.Scheme.Modules
