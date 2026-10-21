/-
Copyright (c) 2026 The Weil Conjectures Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Weil Conjectures Project
-/
module

public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf

/-!
# Filtered colimit cocones of ring objects

Source: blueprint `sec-proetale-coefficients`, proof of `sk-prop-sfb-qlbar-colimit-x`,
paragraph "Third isomorphism"; Stacks Project, Tags 002F, 002V and 0FFK
(blueprint: lem-sfb-filtered-ring-object-cocone-colimit).

## Main statements

* `CategoryTheory.Mon.filtered_cocone_isColimit`: an underlying colimit cocone is colimiting
  in ring objects, and its canonical mediating maps preserve the unit and multiplication.
* `CategoryTheory.CommMon.filtered_cocone_isColimit`: the commutative version, in a braided
  monoidal category.
-/

@[expose] public section

universe v u w

open CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace CategoryTheory

/-- An underlying filtered colimit cocone of ring objects is colimiting in ring objects.
Source: blueprint `sk-prop-sfb-qlbar-colimit-x`, proof, "Third isomorphism"; Stacks Project,
Tags 002F, 002V and 0FFK (blueprint: lem-sfb-filtered-ring-object-cocone-colimit).

Proof: (1) For a competing ring-object cocone `s`, the underlying colimit gives the unique
map `b` with `c_i ≫ b = s_i` (def-weil-pbc-category-colimit). (2) Choose an index using
nonemptiness. Unit preservation by its two legs implies unit preservation by `b`
(sk-def-sfb-ring-object). (3) Multiplication preservation by these legs shows that
`μ_A ≫ b` and `(b ⊗ b) ≫ μ_B` agree after `c_k ⊗ c_k` for each `k`.
(4) Filteredness provides a common successor for `i,j`; cocone naturality and tensor
bifunctoriality (def-sfb-monoidal-category) give agreement after `c_i ⊗ c_j`.
(5) For fixed `i`, preservation by `D(i) ⊗ -` and colimit uniqueness give agreement after
`c_i ⊗ id_A`. (6) Preservation by `- ⊗ A` and colimit uniqueness give the multiplication
equation for `b`. Together with (2), this is `IsMonHom b`.
(7) Bundle `b` as a ring-object morphism. Its factorization and uniqueness follow from the
underlying colimit, since ring-object morphisms are determined by their underlying maps. -/
theorem Mon.filtered_cocone_isColimit
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    {I : Type w} [SmallCategory I] [IsFiltered I]
    [∀ Y : C, PreservesColimitsOfShape I (tensorLeft Y)]
    [∀ Y : C, PreservesColimitsOfShape I (tensorRight Y)]
    {D : I ⥤ Mon C} (c : Cocone D)
    (hc : IsColimit ((Mon.forget C).mapCocone c)) :
    Nonempty (IsColimit c) ∧
      ∀ s : Cocone D,
        IsMonHom (M := c.pt.X) (N := s.pt.X) (hc.desc ((Mon.forget C).mapCocone s)) := by
  sorry

/-- The same underlying cocone is colimiting among commutative ring objects.
Source: blueprint `sk-prop-sfb-qlbar-colimit-x`, proof, "Third isomorphism"; Stacks Project,
Tags 002F, 002V and 0FFK (blueprint: lem-sfb-filtered-ring-object-cocone-colimit).

Proof: forget commutativity and apply the seven-step ring-object argument of
`Mon.filtered_cocone_isColimit`: construct the unique underlying mediator, check its unit
at one index, check its multiplication on diagonal stages, pass to mixed stages using a
common successor, and use preservation of colimits in the two tensor variables successively.
This yields the ring-object colimit. The functor `CommMon.forget₂Mon C` is fully faithful,
so its mediating ring-object morphisms are exactly morphisms of commutative ring objects;
existence and uniqueness therefore give the claimed commutative colimit. -/
theorem CommMon.filtered_cocone_isColimit
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    {I : Type w} [SmallCategory I] [IsFiltered I]
    [∀ Y : C, PreservesColimitsOfShape I (tensorLeft Y)]
    [∀ Y : C, PreservesColimitsOfShape I (tensorRight Y)]
    {D : I ⥤ CommMon C} (c : Cocone D)
    (hc : IsColimit ((CommMon.forget C).mapCocone c)) :
    Nonempty (IsColimit c) := by
  sorry

end CategoryTheory
