/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.Functor
public import WeilConjectures.Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly

/-!
# The open–closed triangle of a recollement-type configuration

Let `C`, `D₁`, `D₂` be pretriangulated categories with adjunctions `j_! ⊣ j^*` (between `D₁`
and `C`) and `i^* ⊣ i_*` (between `C` and `D₂`), where `j^*` and `i^*` are triangulated. Assume

* the unit `𝟭 ⟶ j^* j_!` and the counit `i^* i_* ⟶ 𝟭` are isomorphisms;
* `i^* j_! = 0` and `j^* i_* = 0`;
* `j^*` and `i^*` jointly reflect isomorphisms.

Then for every `M ∈ C` the counit `j_! j^* M ⟶ M` and the unit `M ⟶ i_* i^* M` extend to a
distinguished triangle `j_! j^* M ⟶ M ⟶ i_* i^* M ⟶ (j_! j^* M)[1]`
(`CategoryTheory.Pretriangulated.exists_distTriang_recollement`), whose third morphism is
unique (`CategoryTheory.Pretriangulated.existsUnique_distTriang_recollement`) and natural in `M`
(`CategoryTheory.Pretriangulated.recollementTriangle_comm₃`), because
`Hom((j_! N)[n], i_* P) = 0` for all `n`
(`CategoryTheory.Pretriangulated.eq_zero_of_shift_obj_to_obj_of_adjunction`).

This is the abstract form of the argument of `AlgebraicGeometry.Etale.exists_distTriang_openClosed`;
it applies verbatim to the pro-étale sites at every coefficient stage.
-/

@[expose] public section

universe v u


open CategoryTheory Category Limits

namespace CategoryTheory.Pretriangulated

section Hom

variable {C : Type*} [Category C] [Preadditive C] {D : Type*} [Category D] [Preadditive D]

/-- A morphism `j_! N ⟶ M` vanishes as soon as `j^* M = 0`, for an adjunction `j_! ⊣ j^*`. -/
lemma eq_zero_of_adjunction_of_isZero {jl : D ⥤ C} {ju : C ⥤ D} (adj : jl ⊣ ju)
    [ju.PreservesZeroMorphisms] {N : D} {M : C} (hM : IsZero (ju.obj M))
    (φ : jl.obj N ⟶ M) : φ = 0 :=
  (adj.homEquiv _ _).injective (hM.eq_of_tgt _ _)

variable [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive]

/-- **Hom vanishing.** For an adjunction `j_! ⊣ j^*` with `j^*` commuting with shifts, every
morphism `(j_! N)[n] ⟶ M` vanishes as soon as `j^* M = 0`. -/
lemma eq_zero_of_shift_obj_to_obj_of_adjunction {jl : D ⥤ C} {ju : C ⥤ D} (adj : jl ⊣ ju)
    [ju.Additive] [ju.CommShift ℤ] {N : D} {M : C} (hM : IsZero (ju.obj M)) (n : ℤ)
    (φ : (jl.obj N)⟦n⟧ ⟶ M) : φ = 0 := by
  have h : (shiftFunctorCompIsoId C n (-n) (add_neg_cancel n)).inv.app _ ≫ φ⟦-n⟧' = 0 :=
    eq_zero_of_adjunction_of_isZero adj
      ((shiftFunctor D (-n)).map_isZero hM |>.of_iso ((ju.commShiftIso (-n)).app M)) _
  have h' : φ⟦-n⟧' = (shiftFunctor C (-n)).map 0 := by
    rw [Functor.map_zero]
    simpa using (shiftFunctorCompIsoId C n (-n) (add_neg_cancel n)).hom.app _ ≫= h
  exact (shiftFunctor C (-n)).map_injective h'

end Hom

variable {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- In a pretriangulated category, the third morphism of a distinguished triangle extending
`f : X ⟶ Y` and `g : Y ⟶ Z` is unique as soon as `Hom(X[1], Z) = 0`. -/
lemma existsUnique_distTriang_of_eq_zero {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h₀ : ∀ φ : X⟦(1 : ℤ)⟧ ⟶ Z, φ = 0) (h : ∃ w, Triangle.mk f g w ∈ distTriang C) :
    ∃! w : Z ⟶ X⟦(1 : ℤ)⟧, Triangle.mk f g w ∈ distTriang C := by
  obtain ⟨w, hw⟩ := h
  refine ⟨w, hw, fun w' hw' ↦ ?_⟩
  obtain ⟨c, hc₁, hc₂⟩ := complete_distinguished_triangle_morphism _ _ hw hw' (𝟙 _) (𝟙 _)
    (by simp)
  obtain ⟨φ, hφ⟩ := Triangle.yoneda_exact₃ _ hw (c - 𝟙 _) (by
    rw [Preadditive.comp_sub, hc₁]
    simp)
  rw [h₀ φ, comp_zero, sub_eq_zero] at hφ
  rw [hφ] at hc₂
  simpa using hc₂.symm

/-- In a pretriangulated category, a morphism `(a, b)` between the first two morphisms of two
distinguished triangles `X ⟶ Y ⟶ Z ⟶ X[1]` and `X' ⟶ Y' ⟶ Z' ⟶ X'[1]`, together with a morphism
`c : Z ⟶ Z'` compatible with `b`, is a morphism of triangles as soon as `Hom(X[1], Z') = 0`. -/
lemma comm₃_of_eq_zero {X Y Z X' Y' Z' : C} {f : X ⟶ Y} {g : Y ⟶ Z} {w : Z ⟶ X⟦(1 : ℤ)⟧}
    {f' : X' ⟶ Y'} {g' : Y' ⟶ Z'} {w' : Z' ⟶ X'⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g w ∈ distTriang C) (hT' : Triangle.mk f' g' w' ∈ distTriang C)
    (a : X ⟶ X') (b : Y ⟶ Y') (c : Z ⟶ Z') (ha : f ≫ b = a ≫ f') (hc : g ≫ c = b ≫ g')
    (h₀ : ∀ φ : X⟦(1 : ℤ)⟧ ⟶ Z', φ = 0) :
    w ≫ a⟦(1 : ℤ)⟧' = c ≫ w' := by
  obtain ⟨c', hc₁, hc₂⟩ := complete_distinguished_triangle_morphism _ _ hT hT' a b ha
  obtain ⟨φ, hφ⟩ := Triangle.yoneda_exact₃ _ hT
    (@HSub.hSub (Z ⟶ Z') (Z ⟶ Z') (Z ⟶ Z') _ c' c) (by
    rw [Preadditive.comp_sub, sub_eq_zero]
    exact hc₁.trans hc.symm)
  rw [h₀ φ, comp_zero, sub_eq_zero] at hφ
  rw [hφ] at hc₂
  exact hc₂

variable {D₁ D₂ : Type u} [Category.{v} D₁] [Category.{v} D₂]
  {jl : D₁ ⥤ C} {ju : C ⥤ D₁} {iu : C ⥤ D₂} {il : D₂ ⥤ C}

/-- For adjunctions `j_! ⊣ j^*` and `i^* ⊣ i_*`, the property of a morphism
`w : i_* i^* M ⟶ (j_! j^* M)[1]` that the triangle
`j_! j^* M ⟶ M ⟶ i_* i^* M ⟶ (j_! j^* M)[1]`, formed by the counit of `j_! ⊣ j^*`, the unit of
`i^* ⊣ i_*` and `w`, is distinguished. -/
def IsRecollementTriangle (adj' : jl ⊣ ju) (adj : iu ⊣ il) (M : C)
    (w : il.obj (iu.obj M) ⟶ (jl.obj (ju.obj M))⟦(1 : ℤ)⟧) : Prop :=
  Triangle.mk (adj'.counit.app M) (adj.unit.app M) w ∈ distTriang C

variable [Preadditive D₁] [HasShift D₁ ℤ] [∀ n : ℤ, (shiftFunctor D₁ n).Additive]
  [ju.CommShift ℤ] [ju.Additive]

/-- **Functoriality of the open–closed triangle**: for `φ : M ⟶ M'` and distinguished
open–closed triangles of `M` and `M'`, the triple `(j_! j^* φ, φ, i_* i^* φ)` is a morphism of
triangles (the square formed by the third morphisms commutes), as soon as `j^* i_* = 0`. -/
theorem recollementTriangle_comm₃ (adj' : jl ⊣ ju) (adj : iu ⊣ il)
    (hji : ∀ P, IsZero (ju.obj (il.obj P))) {M M' : C} (φ : M ⟶ M')
    {w : il.obj (iu.obj M) ⟶ (jl.obj (ju.obj M))⟦(1 : ℤ)⟧}
    {w' : il.obj (iu.obj M') ⟶ (jl.obj (ju.obj M'))⟦(1 : ℤ)⟧}
    (hw : IsRecollementTriangle adj' adj M w) (hw' : IsRecollementTriangle adj' adj M' w') :
    w ≫ (jl.map (ju.map φ))⟦(1 : ℤ)⟧' = il.map (iu.map φ) ≫ w' :=
  comm₃_of_eq_zero hw hw' _ φ _ (adj'.counit.naturality φ).symm
    (adj.unit.naturality φ).symm (eq_zero_of_shift_obj_to_obj_of_adjunction adj' (hji _) 1)

variable [HasZeroObject D₁] [Pretriangulated D₁] [ju.IsTriangulated]
  [HasZeroObject D₂] [HasShift D₂ ℤ] [Preadditive D₂]
  [∀ n : ℤ, (shiftFunctor D₂ n).Additive] [Pretriangulated D₂]
  [iu.CommShift ℤ] [iu.IsTriangulated]

omit [ju.Additive] in
/-- **The open–closed triangle.** Let `j_! ⊣ j^*` and `i^* ⊣ i_*` be adjunctions with
triangulated `j^*`, `i^*`, such that the unit of `j_! ⊣ j^*` and the counit of `i^* ⊣ i_*` are
isomorphisms, `i^* j_! = 0`, `j^* i_* = 0`, and `(j^*, i^*)` jointly reflects isomorphisms. Then
for every `M` the counit `j_! j^* M ⟶ M` and the unit `M ⟶ i_* i^* M` extend to a distinguished
triangle.

Complete the counit to a distinguished triangle `j_! j^* M ⟶ M ⟶[g] Y`. Applying `j^*` kills `Y`,
the counit becoming invertible; applying `i^*` makes `g` invertible, as `i^* j_! = 0`. Hence the
unit `Y ⟶ i_* i^* Y` is invertible, by joint conservativity: after `j^*` both ends vanish, and
after `i^*` it is inverse to the counit. By naturality of the unit, `g` followed by
`Y ≅ i_* i^* Y ≅ i_* i^* M` is the unit at `M`. -/
theorem exists_distTriang_recollement (adj' : jl ⊣ ju) (adj : iu ⊣ il) [IsIso adj'.unit]
    [IsIso adj.counit] (hij : ∀ N, IsZero (iu.obj (jl.obj N)))
    (hji : ∀ P, IsZero (ju.obj (il.obj P))) (hc : JointlyReflectIsomorphisms (pairFunctor ju iu))
    (M : C) : ∃ w, IsRecollementTriangle adj' adj M w := by
  obtain ⟨Y, g, h, hT⟩ := distinguished_cocone_triangle (adj'.counit.app M)
  have hε : IsIso (ju.map (adj'.counit.app M)) := by
    rw [← IsIso.inv_eq_of_hom_inv_id (adj'.right_triangle_components M)]
    infer_instance
  have hYj : IsZero (ju.obj Y) :=
    (Triangle.isZero₃_iff_isIso₁ _ (ju.map_distinguished _ hT)).2 hε
  have hgi : IsIso (iu.map g) :=
    (Triangle.isZero₁_iff_isIso₂ _ (iu.map_distinguished _ hT)).1 (hij _)
  have hηY : IsIso (adj.unit.app Y) := by
    refine hc.isIso_of_pairFunctor _ ?_ ?_
    · exact ⟨⟨0, hYj.eq_of_src _ _, (hji _).eq_of_src _ _⟩⟩
    · rw [← IsIso.inv_eq_of_inv_hom_id (adj.left_triangle_components Y)]
      infer_instance
  let e : Y ≅ il.obj (iu.obj M) :=
    asIso (adj.unit.app Y) ≪≫ il.mapIso (asIso (iu.map g)).symm
  have he : g ≫ e.hom = adj.unit.app M := by
    have := adj.unit.naturality g
    dsimp at this
    simp only [e, Iso.trans_hom, asIso_hom, Functor.mapIso_hom, Iso.symm_hom, asIso_inv]
    rw [reassoc_of% this, ← Functor.map_comp, IsIso.hom_inv_id, Functor.map_id, comp_id]
  refine ⟨e.inv ≫ h, isomorphic_distinguished _ hT _ ?_⟩
  exact Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e.symm (by simp)
    (by rw [← he]; simp) (by simp)

/-- **Uniqueness of the open–closed triangle**: under the hypotheses of
`CategoryTheory.Pretriangulated.exists_distTriang_recollement`, the third morphism of the
open–closed triangle is unique, as `Hom((j_! j^* M)[1], i_* i^* M) = 0`. -/
theorem existsUnique_distTriang_recollement (adj' : jl ⊣ ju) (adj : iu ⊣ il) [IsIso adj'.unit]
    [IsIso adj.counit] (hij : ∀ N, IsZero (iu.obj (jl.obj N)))
    (hji : ∀ P, IsZero (ju.obj (il.obj P))) (hc : JointlyReflectIsomorphisms (pairFunctor ju iu))
    (M : C) : ∃! w, IsRecollementTriangle adj' adj M w :=
  existsUnique_distTriang_of_eq_zero _ _
    (eq_zero_of_shift_obj_to_obj_of_adjunction adj' (hji _) 1)
    (exists_distTriang_recollement adj' adj hij hji hc M)

end CategoryTheory.Pretriangulated
