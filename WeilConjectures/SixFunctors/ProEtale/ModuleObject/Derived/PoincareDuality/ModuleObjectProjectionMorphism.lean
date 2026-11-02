/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ModuleObjectProjectionMap
public import WeilConjectures.PoincareDuality.Abstract

/-! Normalization of the canonical module-object projection mate. -/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The module-object mate is invertible exactly when the adjunction projection morphism is.
The oplax tensor map is the same derived pullback tensor comparison, and both
constructions transpose that comparison followed by counit tensor identity.
Source: blueprint sk-thm-sf-pf-adic-projection, definition of the projection mate
(blueprint: lem-sfb-module-object-projection-morphism). -/
theorem isIso_moduleObjectProjectionMap_iff
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) :
    IsIso (moduleObjectProjectionMap Λ f K L) ↔
      IsIso ((derivedUpperStarLowerStarAdjunction Λ f).projectionMorphism K L) := by
  rfl

end AlgebraicGeometry.ProEtale.CondensedRing
