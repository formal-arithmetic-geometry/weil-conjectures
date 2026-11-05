/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedScalarMate.ScalarTensorOrdinaryPullback
import WeilConjectures.AlgebraicGeometry.DerivedScalarMate.ScalarMateOrdinaryModuleRoute
import WeilConjectures.AlgebraicGeometry.DerivedScalarMate.TensorScalarOrdinarySinglePullback

/-! # The ordinary scalar mate square on complexes

Source: Stacks Project, Tags 03EL and 07A4.
(blueprint: lem-sfb-scalar-mate-ordinary-complex-route).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.DerivedScalarMate
section Proof

-- Use countable colimits directly instead of diagram-wide instance search.

attribute [local instance] ordinaryTensorTotal

end Proof

attribute [local irreducible] CategoryTheory.Functor.leftAdjoint proEtaleRingModulePullback
  proEtaleRingExtension proEtaleRingRestrictionPullbackInv
  SheafOfModules.monoidalCategory ordinaryTensorIso ordinaryComplexIso
  HomologicalComplex₂.total CategoryTheory.Functor.mapBifunctorHomologicalComplex
  CochainComplex.mapBifunctorSingle₂Iso
set_option backward.defeqAttrib.useBackward true

end AlgebraicGeometry.Scheme.DerivedScalarMate
