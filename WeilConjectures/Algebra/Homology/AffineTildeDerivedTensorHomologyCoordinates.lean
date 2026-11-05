/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.AffineTildeDerivedTensorMate
import WeilConjectures.Algebra.Homology.AffineTildePushforwardHomologyFactorization
import WeilConjectures.Algebra.Homology.AffineTildeCoefficientPushforwardHomologyCoordinates

/-! # Homology coordinates of the raw affine tensor comparison

Source: Stacks Project, Tags 0DJ8, 06Y6 and 08HY.
(blueprint: lem-pc-affine-tilde-derived-tensor-homology-coordinates). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w wM
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
noncomputable section
namespace AlgebraicGeometry

attribute [local irreducible] Functor.rightDerivedFunctor Functor.rightDerivedFunctorUnit
  affineTildePushforwardComparison
  affinePushforwardCohomologyMapOfComparison

section ExactFunctor
variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  (F : C ⥤ D) [F.Additive] [F.PreservesHomology]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (K : CochainComplex C ℤ) (i : ℤ)

end ExactFunctor

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

end AlgebraicGeometry
