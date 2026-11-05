/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PrincipalOpenCechTotal
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import WeilConjectures.Algebra.Homology.OpenRestrictionAdjunctionExact
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful

/-! # Ordinary representatives for the open-sections comparison

Source: Stacks Project, Tags 08BS and 079V.
-/

@[expose] public section

universe u w v
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
noncomputable section
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance 2000] openComparisonModuleAbelian openComparisonOverModuleAbelian

variable (A : Type u) [CommRing A] (U : (Spec (.of A)).Opens)
  [HasDerivedCategory.{w}
    (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
  [∀ V : (Spec (.of A)).Opens, HasDerivedCategory.{w}
    (SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over V))]
  [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
  [HasDerivedCategory.{v} (ModuleCat.{u} A)]

-- Keep the existing over-site parameter even though the proof needs no derived over-site.

end
end AlgebraicGeometry
