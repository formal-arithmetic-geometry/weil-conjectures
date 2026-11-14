/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Standard.StandardSingleFlatCounitPresentation

import WeilConjectures.AlgebraicGeometry.Standard.StandardSingleFlatCounitUnionPresentation

/-! # Gluing flat counit presentations

Source: Stacks Project, Tags 0DJ9 and 08DR.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Bounded flat presentations glue across a two-open cover.
Source: Stacks Project, Tag 0DJ9, relative Mayer--Vietoris induction step; Tag 08DR,
quasi-compact-open induction. -/
theorem standardSingleFlatCounitOnOpen_union
    {Y B A : Scheme.{u}} (p : Y ⟶ B) [QuasiCompact p] [QuasiSeparated p]
    [IsAffine B] [IsAffine A] (g : A ⟶ B) (U V : Y.Opens)
    (hU : IsCompact (U : Set Y)) (hV : IsAffineOpen V)
    (hPU : StandardSingleFlatCounitOnOpen p g U)
    (hPV : StandardSingleFlatCounitOnOpen p g V)
    (hPUV : StandardSingleFlatCounitOnOpen p g (U ⊓ V)) :
    StandardSingleFlatCounitOnOpen p g (U ⊔ V) := by
  intro N _ hN
  let _ := hU
  let _ := hV
  exact standardSingleFlatCounitPresentation_union_of_open_presentations
    p g U V N hN hPU hPV hPUV

end AlgebraicGeometry
