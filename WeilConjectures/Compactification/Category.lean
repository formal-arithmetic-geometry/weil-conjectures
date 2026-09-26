/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Filtered.Basic
public import WeilConjectures.Compactification.CommonRefinement

/-!

# The category of compactifications

The compactifications of a fixed morphism `f : X ⟶ Y` form a category `Compactification f`,
with the refinements of `WeilConjectures.Compactification.Refinement` as morphisms. This
category is cofiltered as soon as `f` admits a compactification at all: any two objects are
refined by a common one (`AlgebraicGeometry.Compactification.exists_common_refinement`), and
any two parallel refinements are equalized by a further refinement, namely by the
equalizer of the two, which is a closed subscheme of the source because the target of the
two refinements is separated over `Y`.

## Main definitions

- `AlgebraicGeometry.Compactification.category`: the category structure on the
  compactifications of `f`.

## Main results

- `AlgebraicGeometry.Compactification.isCofiltered`: this category is cofiltered.

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Compactification

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- The compactifications of `f : X ⟶ Y` form a category, with the refinements as
morphisms. -/
instance category : Category.{u} (Compactification f) where
  Hom c d := c.Refinement d
  id c := Refinement.id c
  comp r s := r.comp s
  id_comp := Refinement.id_comp
  comp_id := Refinement.comp_id
  assoc := Refinement.comp_assoc

@[simp]
theorem id_hom (c : Compactification f) : Refinement.hom (𝟙 c) = 𝟙 c.Z := rfl

@[simp]
theorem comp_hom {c d e : Compactification f} (r : c ⟶ d) (s : d ⟶ e) :
    (r ≫ s).hom = r.hom ≫ s.hom := rfl

/-- Blueprint `sk-prop-nagata-sketch-comp-category`: The compactification category and
common refinements.

For a quasi-compact `f : X ⟶ Y` admitting a compactification, the category of
compactifications of `f` is cofiltered: any two compactifications admit a common
refinement, and any two parallel refinements are equalized by a further refinement. -/
theorem isCofiltered [QuasiCompact f] [HasCompactification f] :
    IsCofiltered (Compactification f) := by
  sorry

end AlgebraicGeometry.Compactification
