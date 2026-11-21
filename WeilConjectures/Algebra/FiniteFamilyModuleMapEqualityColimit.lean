/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.CategoryTheory.Category.Preorder
import WeilConjectures.Algebra.FiniteFamilyCommonStage
import WeilConjectures.Algebra.Homology.PreorderModuleMapEqualityDescent

/-!
# Simultaneous eventual equality of finitely many module maps

A finite family of equalities of maps over a directed colimit holds at one later stage.

## References

* Stacks Project, Algebra, Tag 05N7, clause (3)
* Stacks Project, More on Algebra, Tag 0BC7 (proof of (1))
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

/-- A finite family of equalities of maps over the colimit holds at one later stage. -/
theorem exists_stage_finite_family_map_eq
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (F : I ⥤ CommRingCat.{u}) [HasColimit F]
    (i : I) {T : Type v} [Finite T]
    (M N : T → ModuleCat.{u} (F.obj i))
    (hM : ∀ t, Module.FinitePresentation (F.obj i) (M t))
    (hN : ∀ t, Module.FinitePresentation (F.obj i) (N t))
    (f g : ∀ t, M t ⟶ N t)
    (h : ∀ t, (extendScalars (colimit.ι F i).hom).map (f t) =
      (extendScalars (colimit.ι F i).hom).map (g t)) :
    ∃ (j : I) (hij : i ≤ j), ∀ t,
      (extendScalars (F.map (homOfLE hij)).hom).map (f t) =
        (extendScalars (F.map (homOfLE hij)).hom).map (g t) := by
  classical
  have hs : ∀ t, ∃ j : I, ∃ hij : i ≤ j,
      (extendScalars (F.map (homOfLE hij)).hom).map (f t) =
        (extendScalars (F.map (homOfLE hij)).hom).map (g t) := by
    intro t
    exact eventually_equal_maps_of_directed_preorder_colimit F i (M t) (N t)
      (hM t) (hN t) (f t) (g t) (h t)
  exact exists_common_stage_of_stage_equalities F i M N f g hs

end ModuleCat
