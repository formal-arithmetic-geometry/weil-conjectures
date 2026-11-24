/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows

/-! # Proper forget-supports with recorded ordinary endpoints
-/

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

attribute [local irreducible] DerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions Functor.rightDerivedFunctor
  Functor.leftDerivedFunctor Functor.mapDerivedCategory AlgebraicGeometry.ProjectiveSpace

/-- The existing proper forget-supports isomorphism, with the ordinary direct-image
endpoint fixed before taking components. -/
noncomputable def ordinaryProperForgetComparison
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] :
    rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ≅ ordinaryFinitePushforward A f :=
  rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) f

end AlgebraicGeometry.Etale
