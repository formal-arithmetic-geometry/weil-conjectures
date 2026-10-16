/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.CategoryTheory.FilteredComplexDecalage

/-! # Complex steps of the canonical decalage filtration

Source: Stacks Project, Tags 015X and 012K.
-/

@[expose] public section

universe u v
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.DecreasingFiltration
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K : CochainComplex C ℤ} (L : DecreasingFiltration K)

/-- The canonical decalage's step, viewed as a complex.
Source: Stacks, Tags 015X and 012K (blueprint: def-sp-filtered-complex-decalage). -/
noncomputable abbrev decalageComplex (a : ℤ) : CochainComplex C ℤ := L.decalage.step a

/-- The canonical inclusion of the decalage step into the ambient complex. -/
noncomputable abbrev decalageι (a : ℤ) : L.decalageComplex a ⟶ K :=
  (L.decalage.step a).arrow

/-- The degreewise subobject of the canonical decalage step. -/
noncomputable abbrev decalageStep (a n : ℤ) : Subobject (K.X n) :=
  L.decalage.complexStep a n

/-- The image of the step inclusion is its prescribed degreewise subobject. -/
theorem decalageι_image (a n : ℤ) :
    imageSubobject ((L.decalageι a).f n) = L.decalageStep a n := rfl

end CategoryTheory.DecreasingFiltration
