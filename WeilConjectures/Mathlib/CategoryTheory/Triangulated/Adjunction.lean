/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.Adjunction

/-!
# The localization triangle of a recollement

Let `C`, `D`, `E` be pretriangulated categories, `i : D ⥤ C` a triangulated functor with right
adjoint `i'` and `j : C ⥤ E` a triangulated functor with right adjoint `j'`. Think of `i` as the
direct image `Ri_*` along a closed immersion, `i'` as `Ri^!`, `j` as the restriction `j^*` to the
complementary open and `j'` as `Rj_*`. Assume

- `j ∘ i = 0`;
- the unit of `i ⊣ i'` and the counit of `j ⊣ j'` are isomorphisms (`i` and `j'` are fully
  faithful);
- an object killed by both `j` and `i'` is zero.

Then for every `L` the counit of `i ⊣ i'` and the unit of `j ⊣ j'` extend to a distinguished
triangle `i i' L ⟶ L ⟶ j' j L ⟶ (i i' L)⟦1⟧`.

## Main statements

- `CategoryTheory.Adjunction.isZero_obj_of_comp_isZero`: `i' ∘ j' = 0`.
- `CategoryTheory.Adjunction.isZero_of_isZero_rightAdjoint`: `j` and `i'` detect zero objects.
- `CategoryTheory.Adjunction.exists_distTriang_counit_unit`: the localization triangle.
-/

@[expose] public section

namespace CategoryTheory

open Limits Pretriangulated

namespace Adjunction

variable {C D E : Type*} [Category* C] [Category* D] [Category* E] [Preadditive D]

variable {i : D ⥤ C} {i' : C ⥤ D} (adjI : i ⊣ i') {j : C ⥤ E} {j' : E ⥤ C} (adjJ : j ⊣ j')

include adjI adjJ in
/-- If `j ∘ i = 0`, then `i' ∘ j' = 0`: maps `N ⟶ i' (j' M)` correspond to maps
`j (i N) ⟶ M`, and `j (i N)` is zero. -/
lemma isZero_obj_of_comp_isZero (hji : ∀ B, IsZero (j.obj (i.obj B))) (M : E) :
    IsZero (i'.obj (j'.obj M)) := by
  rw [IsZero.iff_id_eq_zero]
  have : Subsingleton (i'.obj (j'.obj M) ⟶ i'.obj (j'.obj M)) :=
    ((adjI.homEquiv _ _).symm.trans (adjJ.homEquiv _ _).symm).subsingleton_congr.2
      ⟨(hji _).eq_of_src⟩
  exact Subsingleton.elim _ _

variable [Preadditive C] [Preadditive E] [HasZeroObject C] [HasZeroObject D] [HasZeroObject E]
  [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [∀ n : ℤ, (shiftFunctor E n).Additive]
  [Pretriangulated C] [Pretriangulated D] [Pretriangulated E]
  [i.CommShift ℤ] [i.IsTriangulated] [j.CommShift ℤ] [j.IsTriangulated]

include adjI in
omit [i.CommShift ℤ] [i.IsTriangulated] in
set_option backward.isDefEq.respectTransparency false in
/-- **Detection of zero objects by `j` and `i'`.** Let `k ⊣ i ⊣ i'` with `k` and `j`
triangulated, `j ∘ i = 0` and the counit of `k ⊣ i` an isomorphism. If `j` and `k` jointly
detect zero objects, so do `j` and `i'`.

Let `j X = 0` and `i' X = 0`. The unit `X ⟶ i (k X)` is inverted by `j` (both sides vanish)
and by `k` (the counit is invertible), so its cone is zero and `X ≅ i (k X)`. Then
`Hom(X, X) ≅ Hom(i (k X), X) ≅ Hom(k X, i' X) = 0`. -/
theorem isZero_of_isZero_rightAdjoint {k : C ⥤ D} (adjK : k ⊣ i) [IsIso adjK.counit]
    [k.CommShift ℤ] [k.IsTriangulated]
    (hji : ∀ B, IsZero (j.obj (i.obj B)))
    (hdet : ∀ X, IsZero (j.obj X) → IsZero (k.obj X) → IsZero X) {X : C}
    (hj : IsZero (j.obj X)) (hi : IsZero (i'.obj X)) : IsZero X := by
  obtain ⟨W, v, w, h₁⟩ := distinguished_cocone_triangle (adjK.unit.app X)
  have hku : IsIso (k.map (adjK.unit.app X)) :=
    have := IsIso.id (k.obj X)
    IsIso.of_isIso_fac_right (adjK.left_triangle_components X)
  have hju : IsIso (j.map (adjK.unit.app X)) :=
    isIso_of_source_target_iso_zero _ hj.isoZero (hji _).isoZero
  have hW : IsZero W := hdet _
    ((Triangle.isZero₃_iff_isIso₁ _ (j.map_distinguished _ h₁)).2 hju)
    ((Triangle.isZero₃_iff_isIso₁ _ (k.map_distinguished _ h₁)).2 hku)
  have : IsIso (adjK.unit.app X) := (Triangle.isZero₃_iff_isIso₁ _ h₁).1 hW
  rw [IsZero.iff_id_eq_zero]
  have : Subsingleton (X ⟶ X) :=
    (((asIso (adjK.unit.app X)).homCongr (Iso.refl X)).trans
      (adjI.homEquiv _ _)).subsingleton_congr.2 ⟨hi.eq_of_tgt⟩
  exact Subsingleton.elim _ _

set_option backward.isDefEq.respectTransparency false in
/-- **The localization triangle of a recollement.** Let `i ⊣ i'` and `j ⊣ j'` be adjunctions
between pretriangulated categories with `i` and `j` triangulated, such that `j ∘ i = 0`, the
unit of `i ⊣ i'` and the counit of `j ⊣ j'` are isomorphisms, and `j` and `i'` jointly detect
zero objects. Then for every `L` there is a distinguished triangle

```
  i i' L --ε_L--> L --η_L--> j' j L --w--> (i i' L)⟦1⟧
```

whose first two maps are the counit of `i ⊣ i'` and the unit of `j ⊣ j'`.

Complete `ε_L` to a distinguished triangle `i i' L ⟶ L ⟶ C ⟶`. As `ε_L ≫ η_L = 0` (it factors
through `j' j (i i' L) = 0`), `η_L` factors as `L ⟶ C ⟶[g] j' j L`. The cone `E` of `g` is
killed by `j`, because `j` inverts `L ⟶ C` and `η_L`, and by `i'`, because `i'` kills `C` (it
inverts `ε_L`) and `j' j L` (`i' ∘ j' = 0`). So `E = 0` and `g` is an isomorphism. -/
theorem exists_distTriang_counit_unit (hji : ∀ B, IsZero (j.obj (i.obj B)))
    [IsIso adjI.unit] [IsIso adjJ.counit]
    (hdet : ∀ X, IsZero (j.obj X) → IsZero (i'.obj X) → IsZero X) (L : C) :
    ∃ w, Triangle.mk (adjI.counit.app L) (adjJ.unit.app L) w ∈ distTriang C := by
  let := adjI.rightAdjointCommShift ℤ
  have := adjI.commShift_of_leftAdjoint ℤ
  have := adjI.isTriangulated_rightAdjoint
  have := adjJ.right_adjoint_additive
  obtain ⟨Q, v, w₀, h₁⟩ := distinguished_cocone_triangle (adjI.counit.app L)
  have hεη : adjI.counit.app L ≫ adjJ.unit.app L = 0 := by
    have := adjJ.unit.naturality (adjI.counit.app L)
    dsimp at this
    rw [this, (hji _).eq_of_src (j.map _), Functor.map_zero, Limits.comp_zero]
  obtain ⟨g, hg⟩ := Triangle.yoneda_exact₂ _ h₁ (adjJ.unit.app L) hεη
  obtain ⟨E', h, k, h₂⟩ := distinguished_cocone_triangle g
  have hjv : IsIso (j.map v) :=
    (Triangle.isZero₁_iff_isIso₂ _ (j.map_distinguished _ h₁)).1 (hji _)
  have hjη : IsIso (j.map (adjJ.unit.app L)) :=
    have := IsIso.id (j.obj L)
    IsIso.of_isIso_fac_right (adjJ.left_triangle_components L)
  have hjg : IsIso (j.map g) :=
    IsIso.of_isIso_fac_left (f := j.map v) (h := j.map (adjJ.unit.app L))
      (by rw [hg, Triangle.mk_mor₂, Functor.map_comp])
  have hiε : IsIso (i'.map (adjI.counit.app L)) :=
    have := IsIso.id (i'.obj L)
    IsIso.of_isIso_fac_left (adjI.right_triangle_components L)
  have hiQ : IsZero (i'.obj Q) :=
    (Triangle.isZero₃_iff_isIso₁ _ (i'.map_distinguished _ h₁)).2 hiε
  have hE : IsZero E' := hdet _
    ((Triangle.isZero₃_iff_isIso₁ _ (j.map_distinguished _ h₂)).2 hjg)
    (Triangle.isZero₃_of_isZero₁₂ _ (i'.map_distinguished _ h₂) hiQ
      (isZero_obj_of_comp_isZero adjI adjJ hji _))
  have : IsIso g := (Triangle.isZero₃_iff_isIso₁ _ h₂).1 hE
  refine ⟨inv g ≫ w₀, isomorphic_distinguished _ h₁ _ ?_⟩
  exact Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (asIso g).symm (by simp)
    (by simp [hg]) (by simp)

end Adjunction

end CategoryTheory
