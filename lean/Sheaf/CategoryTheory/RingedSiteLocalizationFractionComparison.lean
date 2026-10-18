/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import Sheaf.CategoryTheory.RingedSiteLocalization
public import Sheaf.CategoryTheory.RingedSectionLocalization

/-! Comparison of the sequential and fraction coefficient localizations. -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

set_option autoImplicit false

namespace CategoryTheory

/-- The sequential colimit coefficient is the sheafified fraction coefficient.

Source: Stacks Project, algebraization.tex, Tag 0997, definition of A_f.
(blueprint: lem-weil-pbc-ringed-site-localization-fraction-comparison).

Proof: On every W → U, send a section x at stage n of the multiplication-by-f
sequence to x/(f|W)^n. These maps form a compatible cocone in the fraction
presheaf. They are linear and commute with restriction, since localization
restriction extends the coefficient ring map. Conversely, for any module
presheaf cocone, send x/f^n to the image of x from stage n. If fractions agree,
multiplication by a sufficiently large power of f makes their cross products
equal; the transition relations in the cocone then identify their images.
This proves well-definedness, linearity, naturality, and uniqueness, so the
fraction presheaf is the colimit of the rank-one presheaf diagram. Sheafify this
colimit. Sheafification is a left adjoint, and its counit identifies the
sheafification of the unit module with the unit module, including its
multiplication endomorphism. The resulting colimit is exactly the recorded
sequential coefficient. The two comparisons are inverse by the colimit
universal property. This proof includes zero and nilpotent f and zero rings.
-/
theorem ringedSite_localization_fraction_comparison
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u}) (U : C) (f : R.obj.obj (op U)) :
    let R₀ := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R
    Nonempty (ringedSiteSectionLocalization R₀ U f ≅
      ringedSectionLocalization (R.over U) (ringedSliceSection R U f)) := by sorry

end CategoryTheory
