/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.AffinePushforwardComparisonCoordinates

public import WeilConjectures.Algebra.Homology.AffineTildePushforwardCohomologyNormalization
import all WeilConjectures.Algebra.Homology.MixedTensorUnderlyingHomology

/-! # Composition of the exact homology comparisons in affine pushforward

Source: Stacks Project, Tags 06Z0 and 0AVW.
(blueprint: lem-pc-affine-tilde-pushforward-homology-factorization). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace AlgebraicGeometry

attribute [local irreducible] Functor.rightDerivedFunctor Functor.rightDerivedFunctorUnit
  affineTildePushforwardComparison

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

end AlgebraicGeometry
