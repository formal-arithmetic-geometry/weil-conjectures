/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.InternalScalarMateProjection
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResiduePullFlatModelMateNormalized
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResiduePullOrdinaryUnit
public import WeilConjectures.AlgebraicGeometry.NormalizedScalarRestrictionPush

/-! # Normalized scalar restriction and direct image

The comparison obtained by uniqueness of right adjoints is the geometric mate of the
canonical exact restriction/pullback comparison.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CategoryTheory.Functor
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.QuotientChange

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory AlgebraicGeometry.ProEtale.upperStarFromPoint

set_option allowUnsafeReducibility true
attribute [local reducible] Functor.mapHomotopyCategory L F
  CondensedRing.moduleObjectDerivedPullback
  CondensedRing.moduleObjectDerivedPushforward

end AlgebraicGeometry.ProEtale.QuotientChange
