/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedScalarMate.ScalarTensorOrdinaryPullback
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.AlgebraicGeometry.DerivedScalarMate.ScalarMateOrdinaryComplexRoute
import WeilConjectures.AlgebraicGeometry.DerivedScalarMate.ScalarMateRestrictionCounitRoute

/-! # The scalar mate in ordinary tensor coordinates

Source: Stacks Project, Tags 03EK, 06YY, 07A4 and 07A6.
(blueprint: lem-sfb-scalar-mate-ordinary-tensor-route).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.DerivedScalarMate
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.leftAdjoint
  proEtaleRingModulePullback
  SheafOfModules.monoidalCategory ordinaryComplexIso ordinaryTensorIso
  proEtaleRingRestrictionDerivedPullback
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] ordinaryScalarIso

end AlgebraicGeometry.Scheme.DerivedScalarMate
