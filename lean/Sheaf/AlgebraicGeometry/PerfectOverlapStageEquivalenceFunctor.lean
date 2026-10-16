/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Sheaf.AlgebraicGeometry.PerfectOverlapStageEquivalence

/-! # The cartesian stage equivalence's forward functor -/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

/-- The forward stage equivalence is pullback along the cartesian scheme
isomorphism. Source: the constructor of `overlapSchemeIsoDerivedEquivalence`. -/
theorem perfectOverlapStageEquivalence_functor_eq
    {X Y S T : Scheme.{u}} (g : X ⟶ Y) (pX : X ⟶ T)
    (pY : Y ⟶ S) (q : T ⟶ S) (h : IsPullback g pX pY q)
    (U V : Y.Opens) :
    (perfectOverlapStageEquivalence g pX pY q h U V).functor =
      derivedPullback
        (((isPullback_morphismRestrict g (U ⊓ V)).paste_vert h).isoPullback.inv) := by
  rfl

end AlgebraicGeometry
