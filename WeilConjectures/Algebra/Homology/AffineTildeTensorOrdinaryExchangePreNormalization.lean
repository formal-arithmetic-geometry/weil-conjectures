/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.AffinePushforwardComparisonCoordinates

public import WeilConjectures.Algebra.Homology.AffineTildeTensorSourceComparison
public import WeilConjectures.Algebra.Homology.AffineBaseChangeTildeRepresentative
import WeilConjectures.Algebra.Homology.AffineTildePushforwardCohomologyNormalization
import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeUnitCompatibility
import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import WeilConjectures.AlgebraicGeometry.TensorPullbackTilde
public import
  WeilConjectures.Algebra.Homology.AffineTildeTensorOrdinaryExchangePreNormalizationChain

/-! The derived equality before target-map expansion and direct-image reassociation. -/
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings
noncomputable section
namespace AlgebraicGeometry

attribute [local instance 2000] chainCoordinatesCategory chainCoordinatesPreadditive
  chainCoordinatesAbelian

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

attribute [local irreducible] affineTildePushforwardComparison
  Functor.rightDerivedFunctor Functor.rightDerivedFunctorUnit
  Scheme.Modules.tensorPullback
  affineTildeTensorOrdinarySourceIso

end AlgebraicGeometry
