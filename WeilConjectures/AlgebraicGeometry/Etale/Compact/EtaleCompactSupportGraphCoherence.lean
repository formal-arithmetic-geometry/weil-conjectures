/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportGraphDerivedIsoSupplement
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportNormalizationDataSupplement
import all WeilConjectures.AlgebraicGeometry.EtaleCompactSupportGraphGeometricBaseChange
import all WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import all WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjectionBaseChange
import all WeilConjectures.SixFunctors.Etale.Derived.EtaleLowerShriekBaseChange
import all WeilConjectures.SixFunctors.Etale.Derived.BaseChangeCube
import all WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedProperOpenCompositionSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-!
# Coherence of the specified compact-support graph map

Source: SGA 4 XVII 5.2.2, 6.2.11; Stacks Project Tags 03S6, 0F7B and 0F7C
(blueprint: lem-asd-compact-support-graph-coherence).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v w

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local instance 2000] Abelian.toPreadditive

attribute [local irreducible] upperStar lowerStar
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor

attribute [local instance 2000] Abelian.toPreadditive

end AlgebraicGeometry.Etale
