/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

set_option linter.style.haveILetI false in
/-- Equality to zero in a filtered colimit of additive groups is detected at a later
stage.
Source: Stacks Project, Tag 0739, filtered-colimit equality criterion.
(blueprint: lem-sc-filtered-colimit-map-zero)

Proof: apply the concrete filtered-colimit equality criterion to the element and
zero, then simplify the image of zero under the transition homomorphism. -/
theorem exists_filteredColimit_map_eq_zero
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (H : I ⥤ AddCommGrpCat.{u + 1}) (t : Cocone H) (ht : IsColimit t)
    (i : I) (x : H.obj i) (hx : (t.ι.app i).hom x = 0) :
    ∃ (j : I) (a : i ⟶ j), (H.map a).hom x = 0 := by
  letI : PreservesFilteredColimitsOfSize.{u, u} (forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u} _
  have h := (ht.eq_iff' x (0 : H.obj i)).mp (by simpa only [map_zero] using hx)
  obtain ⟨j, a, ha⟩ := h
  refine ⟨j, a, ?_⟩
  simpa using ha

end AlgebraicGeometry.Etale
