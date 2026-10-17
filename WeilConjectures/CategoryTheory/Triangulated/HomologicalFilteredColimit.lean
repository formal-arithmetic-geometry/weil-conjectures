/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor

/-!
# Homological functors and colimits of triangles

Let `F : C ⥤ A` be a homological functor from a pretriangulated category to an abelian category
in which colimits of shape `I` exist and are exact. For a functor `G : I ⥤ C` and a cocone `s`
on `G` (in `C`, where `s` need not be a colimit), say that `F` is *continuous* on `s`
(`CategoryTheory.Functor.IsContinuousOn`) if for every `n` the comparison map
`colim_i F_n(G i) ⟶ F_n(s.pt)` is an isomorphism, `F_n` being the shifted functors of `F`.

Given a functor `T : I ⥤ Triangle C` with distinguished values and a cocone on `T` with
distinguished point, continuity on two of the three vertices implies continuity on the third
(`CategoryTheory.Functor.IsContinuousOn.of_triangle₂` and its rotations): the long exact
sequences of `F` pass to the colimit, colimits of shape `I` being exact, and the four lemmas
apply.
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated ComposableArrows

namespace CategoryTheory

namespace ComposableArrows

variable {I A : Type*} [Category I] [Category A] [Abelian A] [HasColimitsOfShape I A]
  [HasExactColimitsOfShape I A]

lemma exact_flip_comp_colim {n : ℕ} (S : I ⥤ ComposableArrows A n) (hS : ∀ i, (S.obj i).Exact) :
    ComposableArrows.Exact (S.flip ⋙ colim : ComposableArrows A n) := by
  have hc : ComposableArrows.IsComplex (S.flip : ComposableArrows (I ⥤ A) n) :=
    ⟨fun k hk ↦ by
      ext j
      exact (hS j).toIsComplex.zero k hk⟩
  refine ⟨⟨fun k hk ↦ ?_⟩, fun k hk ↦ ?_⟩
  · change colim.map _ ≫ colim.map _ = 0
    rw [← Functor.map_comp, hc.zero k hk, Functor.map_zero]
  · have hex : (ComposableArrows.sc (S.flip : ComposableArrows (I ⥤ A) n) hc k hk).Exact := by
      rw [ShortComplex.exact_iff_isZero_homology, Functor.isZero_iff]
      intro j
      exact IsZero.of_iso ((ShortComplex.exact_iff_isZero_homology _).1 ((hS j).exact k hk))
        ((ComposableArrows.sc (S.flip : ComposableArrows (I ⥤ A) n) hc k hk).mapHomologyIso
          ((evaluation I A).obj j)).symm
    exact hex.map colim

end ComposableArrows

namespace Functor

variable {C A I : Type*} [Category C] [Category A] [Category I]
  [HasZeroObject C] [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [Abelian A] (F : C ⥤ A) [F.IsHomological] [F.ShiftSequence ℤ]
  [HasColimitsOfShape I A]

/-- A homological functor `F` is *continuous* on a cocone `s` on `G : I ⥤ C` if for every `n` the
comparison map `colim_i F_n(G i) ⟶ F_n(s.pt)` is an isomorphism. -/
def IsContinuousOn {G : I ⥤ C} (s : Cocone G) : Prop :=
  ∀ n : ℤ, IsIso (colimit.desc (G ⋙ F.shift n) ((F.shift n).mapCocone s))

/-- The long exact sequence `F_{n₀}(T₁) → F_{n₀}(T₂) → F_{n₀}(T₃) → F_{n₁}(T₁) → F_{n₁}(T₂) →
F_{n₁}(T₃)`, functorially in the triangle `T`. -/
@[simps]
noncomputable def homologySequenceComposableArrows₅Functor (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    Triangle C ⥤ ComposableArrows A 5 where
  obj T := F.homologySequenceComposableArrows₅ T n₀ n₁ h
  map {T T'} φ := homMk₅ ((F.shift n₀).map φ.hom₁) ((F.shift n₀).map φ.hom₂)
    ((F.shift n₀).map φ.hom₃) ((F.shift n₁).map φ.hom₁) ((F.shift n₁).map φ.hom₂)
    ((F.shift n₁).map φ.hom₃)
    (by
      change (F.shift n₀).map T.mor₁ ≫ _ = _ ≫ (F.shift n₀).map T'.mor₁
      rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₁])
    (by
      change (F.shift n₀).map T.mor₂ ≫ _ = _ ≫ (F.shift n₀).map T'.mor₂
      rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₂])
    (by
      change F.homologySequenceδ T n₀ n₁ h ≫ _ = _ ≫ F.homologySequenceδ T' n₀ n₁ h
      exact (F.homologySequenceδ_naturality T T' φ n₀ n₁ h).symm)
    (by
      change (F.shift n₁).map T.mor₁ ≫ _ = _ ≫ (F.shift n₁).map T'.mor₁
      rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₁])
    (by
      change (F.shift n₁).map T.mor₂ ≫ _ = _ ≫ (F.shift n₁).map T'.mor₂
      rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₂])
  map_id T := by apply hom_ext₅ <;> exact Functor.map_id _ _
  map_comp φ ψ := by apply hom_ext₅ <;> exact Functor.map_comp _ _ _

variable [HasExactColimitsOfShape I A] {F}

variable (T : I ⥤ Triangle C) (hT : ∀ i, T.obj i ∈ distTriang C) (s : Cocone T)
  (hs : s.pt ∈ distTriang C)

/-- The comparison from the colimit of the long exact sequences of the `T i` to the long exact
sequence of `s.pt`. -/
noncomputable def colimitHomologySequenceComparison (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    ((T ⋙ F.homologySequenceComposableArrows₅Functor n₀ n₁ h).flip ⋙ colim :
        ComposableArrows A 5) ⟶
      F.homologySequenceComposableArrows₅ s.pt n₀ n₁ h where
  app k := colimit.desc _
    (((evaluation _ A).obj k).mapCocone ((F.homologySequenceComposableArrows₅Functor n₀ n₁
      h).mapCocone s))
  naturality k k' f := by
    apply colimit.hom_ext
    intro i
    erw [ι_colimMap_assoc, colimit.ι_desc, colimit.ι_desc_assoc]
    exact ((F.homologySequenceComposableArrows₅Functor n₀ n₁ h).map (s.ι.app i)).naturality f

include hT hs in
/-- **Two out of three**: continuity on the first and third vertices of a colimit of triangles
implies continuity on the second. -/
lemma IsContinuousOn.of_triangle₂ (h₁ : F.IsContinuousOn (Triangle.π₁.mapCocone s))
    (h₃ : F.IsContinuousOn (Triangle.π₃.mapCocone s)) :
    F.IsContinuousOn (Triangle.π₂.mapCocone s) := by
  intro n
  have hex (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :=
    ComposableArrows.exact_flip_comp_colim
      (T ⋙ F.homologySequenceComposableArrows₅Functor n₀ n₁ h)
      (fun i ↦ F.homologySequenceComposableArrows₅_exact _ (hT i) n₀ n₁ h)
  have hex' (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) := F.homologySequenceComposableArrows₅_exact _ hs n₀ n₁ h
  have hm : Mono (colimit.desc ((T ⋙ Triangle.π₂) ⋙ F.shift n)
      ((F.shift n).mapCocone (Triangle.π₂.mapCocone s))) := by
    have := Abelian.mono_of_epi_of_mono_of_mono'' (k := 2) (by omega)
      (hex (n - 1) n (by omega)) (hex' (n - 1) n (by omega))
      (colimitHomologySequenceComparison T s (n - 1) n (by omega)) 2 3 4 5 rfl rfl rfl rfl
      (by have := h₃ (n - 1); exact this.epi_of_iso) (by have := h₁ n; exact this.mono_of_iso)
      (by have := h₃ n; exact this.mono_of_iso)
    exact this
  have he : Epi (colimit.desc ((T ⋙ Triangle.π₂) ⋙ F.shift n)
      ((F.shift n).mapCocone (Triangle.π₂.mapCocone s))) := by
    have := Abelian.epi_of_epi_of_epi_of_mono'' (k := 0) (by omega)
      (hex n (n + 1) rfl) (hex' n (n + 1) rfl)
      (colimitHomologySequenceComparison T s n (n + 1) rfl) 0 1 2 3 rfl rfl rfl rfl
      (by have := h₁ n; exact this.epi_of_iso) (by have := h₃ n; exact this.epi_of_iso)
      (by have := h₁ (n + 1); exact this.mono_of_iso)
    exact this
  exact isIso_of_mono_of_epi _

section Transport

variable {B : Type*} [Category B] [HasColimitsOfShape I B]

omit [HasColimitsOfShape I A] [HasExactColimitsOfShape I A] in
/-- The comparison map `colim_i K(G i) ⟶ K(s.pt)` is an isomorphism for one cocone if and only if
it is for an isomorphic cocone over an isomorphic diagram. -/
lemma isIso_colimitDesc_iff_of_iso {G G' : I ⥤ C} (α : G ≅ G') {s : Cocone G}
    {s' : Cocone G'} (β : s.pt ≅ s'.pt) (hβ : ∀ i, s.ι.app i ≫ β.hom = α.hom.app i ≫ s'.ι.app i)
    (K : C ⥤ B) :
    IsIso (colimit.desc (G ⋙ K) (K.mapCocone s)) ↔
      IsIso (colimit.desc (G' ⋙ K) (K.mapCocone s')) := by
  have h : colimit.desc (G ⋙ K) (K.mapCocone s) =
      (HasColimit.isoOfNatIso (Functor.isoWhiskerRight α K)).hom ≫
        colimit.desc (G' ⋙ K) (K.mapCocone s') ≫ K.map β.inv := by
    apply colimit.hom_ext
    intro i
    simp only [colimit.ι_desc, Functor.mapCocone_ι_app, HasColimit.isoOfNatIso_ι_hom_assoc,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, colimit.ι_desc_assoc,
      Functor.comp_obj, ← Functor.map_comp]
    congr 1
    rw [← Category.assoc, ← hβ, Category.assoc, β.hom_inv_id]
    exact (Category.comp_id _).symm
  rw [h]
  constructor
  · intro _
    have : IsIso (colimit.desc (G' ⋙ K) (K.mapCocone s') ≫ K.map β.inv) :=
      IsIso.of_isIso_comp_left (HasColimit.isoOfNatIso (Functor.isoWhiskerRight α K)).hom _
    exact IsIso.of_isIso_comp_right _ (K.map β.inv)
  · intro _
    infer_instance

omit [HasColimitsOfShape I A] [HasExactColimitsOfShape I A] in
/-- The comparison map for `K` is an isomorphism if and only if it is for an isomorphic
functor `K'`. -/
lemma isIso_colimitDesc_iff_of_natIso {G : I ⥤ C} (s : Cocone G) {K K' : C ⥤ B} (e : K ≅ K') :
    IsIso (colimit.desc (G ⋙ K) (K.mapCocone s)) ↔
      IsIso (colimit.desc (G ⋙ K') (K'.mapCocone s)) := by
  have h : colimit.desc (G ⋙ K) (K.mapCocone s) =
      (HasColimit.isoOfNatIso (Functor.isoWhiskerLeft G e)).hom ≫
        colimit.desc (G ⋙ K') (K'.mapCocone s) ≫ e.inv.app s.pt := by
    apply colimit.hom_ext
    intro i
    simp
  rw [h]
  constructor
  · intro _
    have : IsIso (colimit.desc (G ⋙ K') (K'.mapCocone s) ≫ e.inv.app s.pt) :=
      IsIso.of_isIso_comp_left (HasColimit.isoOfNatIso (Functor.isoWhiskerLeft G e)).hom _
    exact IsIso.of_isIso_comp_right _ (e.inv.app s.pt)
  · intro _
    infer_instance

end Transport

omit [HasExactColimitsOfShape I A] in
/-- Continuity on a cocone implies continuity on its shifts. -/
lemma IsContinuousOn.shift {G : I ⥤ C} {s : Cocone G} (hs : F.IsContinuousOn s) (a : ℤ) :
    F.IsContinuousOn ((shiftFunctor C a).mapCocone s) := by
  intro n
  have := hs (a + n)
  exact (isIso_colimitDesc_iff_of_natIso s (F.shiftIso a n (a + n) rfl).symm).1 this

include hT hs in
/-- **Two out of three**: continuity on the second and third vertices of a colimit of triangles
implies continuity on the first. -/
lemma IsContinuousOn.of_triangle₁ (h₂ : F.IsContinuousOn (Triangle.π₂.mapCocone s))
    (h₃ : F.IsContinuousOn (Triangle.π₃.mapCocone s)) :
    F.IsContinuousOn (Triangle.π₁.mapCocone s) :=
  IsContinuousOn.of_triangle₂ (T ⋙ Pretriangulated.invRotate C)
    (fun i ↦ inv_rot_of_distTriang _ (hT i)) ((Pretriangulated.invRotate C).mapCocone s)
    (inv_rot_of_distTriang _ hs) (h₃.shift (-1)) h₂

end Functor

end CategoryTheory
