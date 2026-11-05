/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PinnedPullbackCounitShifts
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.AlgebraicGeometry.PinnedPullbackCompositionShifts
import WeilConjectures.AlgebraicGeometry.PinnedDerivedAdjunctionShifts

/-! # Shift compatibility of the canonical derived base-change mate
Source: Stacks Project, Tag 08HY.
(blueprint: lem-pc-pinned-base-change-mate-shifts). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory
noncomputable section
namespace AlgebraicGeometry
set_option backward.isDefEq.respectTransparency.types false

private theorem pullback_eqToHom_commShift
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (s : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), (derivedPullback.{u, w} f).CommShift ℤ)
    {X Y : Scheme.{u}} {k l : X ⟶ Y} (h : k = l) :
    letI := s k
    letI := s l
    NatTrans.CommShift (eqToHom (congrArg (fun f ↦ derivedPullback.{u, w} f) h)) ℤ := by
  subst l
  simp only [eqToHom_refl]
  infer_instance

end AlgebraicGeometry
