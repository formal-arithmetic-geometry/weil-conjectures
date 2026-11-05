/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeMayerVietorisMaps
public import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisCanonicalData

/-! # SES boundaries and adjunction-compatible shifts for relative Mayer--Vietoris

Source: Stacks Project, Tags 08BV, 08HY and 0DJ9.
(blueprint: def-pc-rf-mv-canonical-ses-shifts).
-/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits TopologicalSpace Pretriangulated
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace AlgebraicGeometry

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- Pullback shifts are the unique mates of the right-derived direct-image shifts
under exactly the adjunction used by the base-change map.
Source: Stacks Tags 079W and 08HY; Mathlib Shift.Adjunction.
(blueprint: def-pc-rf-mv-canonical-ses-shifts). -/
@[instance_reducible] def mvCanonicalPullbackShift {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (derivedPullback g).CommShift ℤ :=
  (mvDerivedPullbackAdjunction g).leftAdjointCommShift ℤ

/-- Composite of the right-derived direct-image shift and its adjoint-compatible
pullback shift. Source: Stacks Tag 0DJ9
(blueprint: def-pc-rf-mv-canonical-ses-shifts). -/
@[instance_reducible] def mvCanonicalSourceShift {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) :
    (schemeDerivedDirectImage f ⋙ derivedPullback g).CommShift ℤ :=
  letI := mvCanonicalPullbackShift g
  inferInstance

end AlgebraicGeometry
