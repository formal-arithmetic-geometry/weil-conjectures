/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawTrianglePullback

import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

public import
  WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.CohomPresheaf

/-! # Raw pullback for a commutative triangle

Source: Stacks Project, Tags 03Q8 and 09Z1, canonical comparison maps.
(blueprint: sbc-lem-higher-image-raw-triangle-restriction).
-/

@[expose] public section

universe u
open CategoryTheory Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

/-- The two source factors of the raw triangle map, kept as one morphism.
Source: Stacks Project, Tags 03Q8 and 09Z1.
(blueprint: sbc-lem-higher-image-raw-triangle-restriction). -/
def rawTriangleSource
    {C D E D' E' : Type*}
    [Category C] [Category D] [Category E] [Category D'] [Category E']
    (H : C ⥤ D) (H' : C ⥤ E) (P : D ⥤ E)
    (A : D ⥤ D') (B : E ⥤ E') (F : D' ⥤ E')
    (c : H' ⟶ H ⋙ P) (e : P ⋙ B ⟶ A ⋙ F) (U : C) :
    B.obj (H'.obj U) ⟶ F.obj (A.obj (H.obj U)) :=
  B.map (c.app U) ≫ e.app (H.obj U)

end AlgebraicGeometry.Etale
