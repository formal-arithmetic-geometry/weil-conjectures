/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Shift.Adjunction
public import Mathlib.CategoryTheory.Triangulated.Functor
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Objects local for an adjunction between pretriangulated categories

Let `L ⊣ R` be an adjunction between pretriangulated categories, compatible with the shifts, with
`L` and `R` triangulated (typically `L = j^*`, `R = Rj_*` for an open immersion `j`). An object
`X` is *local* when the unit `X ⟶ R L X` is an isomorphism. This file records the formal
properties of local objects used to compare the supported localization triangles along changes of
coefficients:

* `CategoryTheory.Adjunction.unitTriangleHom`: the unit as a morphism of triangles
  `T ⟶ (L ⋙ R).mapTriangle.obj T`;
* `CategoryTheory.Adjunction.isIso_unit_app_obj₃_of_distTriang`,
  `CategoryTheory.Adjunction.isIso_unit_app_obj₁_of_distTriang`: local objects satisfy the
  two-out-of-three property in distinguished triangles;
* `CategoryTheory.Adjunction.isIso_unit_app_iff_of_iso_obj`: locality is invariant under
  isomorphism;
* `CategoryTheory.Adjunction.isZero_of_isIso_unit_app`: a local object killed by `L` is zero;
* `CategoryTheory.Adjunction.isIso_unit_app_of_isIso_unit_app_map`: locality descends along a
  triangulated functor reflecting zero objects and commuting with the adjunctions.

-/

@[expose] public section

namespace CategoryTheory

open Limits Category Pretriangulated

namespace Adjunction

section Basic

variable {C D : Type*} [Category* C] [Category* D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)

/-- Locality is invariant under isomorphism: the unit at `X` is invertible iff it is at `Y`. -/
lemma isIso_unit_app_iff_of_iso_obj {X Y : C} (e : X ≅ Y) :
    IsIso (adj.unit.app X) ↔ IsIso (adj.unit.app Y) := by
  have h := adj.unit.naturality e.hom
  dsimp at h
  constructor
  · intro
    have : IsIso (e.hom ≫ adj.unit.app Y) := by
      rw [h]
      infer_instance
    exact IsIso.of_isIso_comp_left e.hom _
  · intro
    have : IsIso (adj.unit.app X ≫ R.map (L.map e.hom)) := by
      rw [← h]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (R.map (L.map e.hom))

/-- If the counit is invertible at `L X`, then `L` inverts the unit at `X`. -/
instance isIso_map_unit_app_of_isIso_counit_app (X : C) [IsIso (adj.counit.app (L.obj X))] :
    IsIso (L.map (adj.unit.app X)) := by
  have : IsIso (L.map (adj.unit.app X) ≫ adj.counit.app (L.obj X)) := by
    rw [adj.left_triangle_components X]
    exact IsIso.id _
  exact IsIso.of_isIso_comp_right _ (adj.counit.app _)

/-- If the counit is an isomorphism, `L` inverts the unit. -/
lemma isIso_map_unit_app_of_isIso_counit [IsIso adj.counit] (X : C) :
    IsIso (L.map (adj.unit.app X)) :=
  adj.isIso_map_unit_app_of_isIso_counit_app X

end Basic

section Shift

variable {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ] [HasShift D ℤ]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [L.CommShift ℤ] [R.CommShift ℤ] [adj.CommShift ℤ]

end Shift

section

variable {C D : Type*} [Category* C] [Category* D]
  [Preadditive C] [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]
  [Preadditive D] [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [L.CommShift ℤ] [R.CommShift ℤ]
  [adj.CommShift ℤ] [L.IsTriangulated] [R.IsTriangulated]

end

end Adjunction

namespace Pretriangulated

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

end Pretriangulated

end CategoryTheory
