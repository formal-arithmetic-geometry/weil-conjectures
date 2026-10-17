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
    (S.flip ⋙ colim : ComposableArrows A n).Exact := by
  have hc : (S.flip : ComposableArrows (I ⥤ A) n).IsComplex :=
    ⟨fun k hk ↦ by
      ext j
      exact (hS j).toIsComplex.zero k hk⟩
  refine ⟨⟨fun k hk ↦ ?_⟩, fun k hk ↦ ?_⟩
  · change colim.map _ ≫ colim.map _ = 0
    rw [← Functor.map_comp, hc.zero k hk, Functor.map_zero]
  · have hex : (hc.sc k hk).Exact := by
      rw [ShortComplex.exact_iff_isZero_homology, Functor.isZero_iff]
      intro j
      rw [((hc.sc k hk).mapHomologyIso ((evaluation I A).obj j)).symm.isZero_iff,
        ← ShortComplex.exact_iff_isZero_homology]
      exact (hS j).exact k hk
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
    (by dsimp; rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₁])
    (by dsimp; rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₂])
    (by dsimp; rw [F.homologySequenceδ_naturality])
    (by dsimp; rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₁])
    (by dsimp; rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₂])
  map_id T := by ext k; fin_cases k <;> simp
  map_comp φ ψ := by ext k; fin_cases k <;> simp

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
    ext i
    simp [← NatTrans.naturality]

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
  have hm : Mono (colimit.desc (Triangle.π₂.mapCocone s).diagram ⋙ F.shift n
      ((F.shift n).mapCocone (Triangle.π₂.mapCocone s))) := by
    have := ComposableArrows.Abelian.mono_of_epi_of_mono_of_mono'' (k := 2) (by omega)
      (hex (n - 1) n (by omega)) (hex' (n - 1) n (by omega))
      (colimitHomologySequenceComparison T s (n - 1) n (by omega)) 2 3 4 5 rfl rfl rfl rfl
      (by have := h₃ (n - 1); exact this.epi_of_iso) (by have := h₁ n; exact this.mono_of_iso)
      (by have := h₃ n; exact this.mono_of_iso)
    exact this
  have he : Epi (colimit.desc (Triangle.π₂.mapCocone s).diagram ⋙ F.shift n
      ((F.shift n).mapCocone (Triangle.π₂.mapCocone s))) := by
    have := ComposableArrows.Abelian.epi_of_epi_of_epi_of_mono'' (k := 0) (by omega)
      (hex n (n + 1) rfl) (hex' n (n + 1) rfl)
      (colimitHomologySequenceComparison T s n (n + 1) rfl) 0 1 2 3 rfl rfl rfl rfl
      (by have := h₁ n; exact this.epi_of_iso) (by have := h₃ n; exact this.epi_of_iso)
      (by have := h₁ (n + 1); exact this.mono_of_iso)
    exact this
  exact isIso_of_mono_of_epi _

end Functor

end CategoryTheory
