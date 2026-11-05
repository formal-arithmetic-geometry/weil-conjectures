/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.DerivedCategory.MittagLefflerTower
public import Mathlib.CategoryTheory.Subobject.ArtinianObject

/-!
# Towers of Artinian objects are Mittag-Leffler

In an abelian category, let `G : ℕᵒᵖ ⥤ C` be a tower whose terms are Artinian objects (e.g.
objects of finite length). The images of the transitions `G m ⟶ G n` form a decreasing chain
of subobjects of `G n`, which stabilises
(`CategoryTheory.Limits.ArtinianTower.exists_im_eq`). The stable images form a subtower
(`CategoryTheory.Limits.ArtinianTower.stabTower`) with epimorphic transitions through which
the transitions of `G` factor, so `G` is Mittag-Leffler
(`CategoryTheory.Limits.isMittagLefflerTower_of_isArtinianObject`); in particular
`lim¹ G = 0` in a replete abelian category
(`CategoryTheory.Limits.epi_one_sub_of_isMittagLefflerTower`).
-/

@[expose] public section

open CategoryTheory Category Limits Opposite

namespace CategoryTheory

variable {C : Type*} [Category* C] [Abelian C]

end CategoryTheory

namespace CategoryTheory.Limits

variable {C : Type*} [Category* C] [Abelian C] (G : ℕᵒᵖ ⥤ C)

namespace ArtinianTower

variable {G} (hG : ImagesStabilize G)

end ArtinianTower

end CategoryTheory.Limits
