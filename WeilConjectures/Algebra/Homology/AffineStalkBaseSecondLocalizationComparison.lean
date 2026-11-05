/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.Algebra.Homology.BaseDerivedTensorRestrictedRingComparison
import WeilConjectures.Algebra.Homology.DerivedTensorBaseSecondLocalizationModels

/-! # Base and second-factor localization after taking the affine input stalk

Source: Stacks Project, Tags 0DJ8 and 06Y6.
(blueprint: new-affine-stalk-base-second-localization-comparison). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w wM
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings
attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local irreducible] AlgebraicGeometry.SingleComplexBaseChange.tensorMap
  AlgebraicGeometry.SingleComplexBaseChange.cohomologyModel
  ModuleCat.baseDerivedTensorCohomologyModel
noncomputable section
namespace AlgebraicGeometry

/-- Changing equal coefficient maps fixes pure tensors. -/
@[irreducible] private def equalCoefficientComplexIso
    (S T : Type u) [CommRing S] [CommRing T] (f g : S →+* T) (h : f = g)
    (Q : CochainComplex (ModuleCat.{u} S) ℤ) :
    ((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj Q ≅
      ((ModuleCat.extendScalars g).mapHomologicalComplex (.up ℤ)).obj Q :=
  eqToIso (congrArg
    (fun k : S →+* T ↦ ((ModuleCat.extendScalars k).mapHomologicalComplex (.up ℤ)).obj Q) h)

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

end AlgebraicGeometry
