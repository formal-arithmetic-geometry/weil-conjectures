/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.HigherImageCohomologySquareRawMap
@[expose] public section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale
/-- Shift-comparison naturality used when moving the coefficient suffix through
 the derived square mate.  This is independent of the test-object geometry.
Source: Stacks Project, Tag 07A7.
(blueprint: lem-sf-higher-image-cohomology-square-coefficient-shift-naturality). -/
theorem higherImageCohomologySquare_coefficient_shift_naturality
    {C : Type u} {D : Type v} [Category.{w} C] [Category.{w} D]
    [HasShift C ℤ] [HasShift D ℤ]
    (F : C ⥤ D) [F.CommShift ℤ] (n : ℤ)
    {X Y : C} (f : X ⟶ Y) :
    (F.commShiftIso n).hom.app X ≫ (shiftFunctor D n).map (F.map f) =
      F.map ((shiftFunctor C n).map f) ≫ (F.commShiftIso n).hom.app Y := by
  simpa only [Functor.comp_map] using (F.commShiftIso n).hom.naturality f |>.symm
end AlgebraicGeometry.Etale
