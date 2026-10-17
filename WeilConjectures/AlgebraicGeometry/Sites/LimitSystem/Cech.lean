/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
public import WeilConjectures.AlgebraicGeometry.Sites.LimitSystem.Sections
public import WeilConjectures.CategoryTheory.Sites.CechComplexTransport
public import WeilConjectures.CategoryTheory.Sites.CechCriterionGood

/-!
# Čech complexes of the colimit of a system of injective sheaves

Let `(Eᵢ)` be a system of injective abelian étale sheaves over a directed inverse system of
quasi-compact quasi-separated schemes `Dᵢ` with affine transition maps and limit `X`, and let `L`
be the colimit on `X` of the pullbacks of the `Eᵢ`. For a finite family `U` of quasi-compact
quasi-separated étale schemes over a stage `D_{i₀}`, the Čech complex of the pushforward of `L` to
`D_{i₀}` on `U` is exact in positive degrees
(`AlgebraicGeometry.Etale.SystemData.exactAt_cechComplex_lowerStar_of_injective`): a cocycle comes
from a cocycle of some pushforward `(D_{i₀} ⟵ Dⱼ)_* Eⱼ`, which is injective.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Presheaf

namespace AlgebraicGeometry.Etale.SystemData

variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
  {D : Iᵒᵖ ⥤ Scheme.{u}} {c : Cone D} (hc : IsLimit c)
  [∀ i : Iᵒᵖ, CompactSpace (D.obj i)] [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
  [∀ (i j : Iᵒᵖ) (f : i ⟶ j), IsAffineHom (D.map f)] (S : SystemData D c)

include hc in
/-- Every section of `L` over `U ×_{D_{i₀}} X` comes from a section of `Fₗ` over
`U ×_{D_{i₀}} Dₗ`, for every large enough stage `l`. -/
lemma exists_stageMap_app_eq_of_le {i₀ : I} (U : (D.obj (op i₀)).Etale) [CompactSpace U.left]
    [QuasiSeparatedSpace U.left]
    (s : ((lowerStar AddCommGrpCat.{u + 1} (c.π.app (op i₀))).obj S.L.pt).obj.obj (op U)) :
    ∃ j : I, ∀ (l : I) (f : i₀ ⟶ l), j ≤ l →
      ∃ t : (S.stageSheaf f).obj.obj (op U), (S.stageMap f).hom.app (op U) t = s := by
  obtain ⟨j, f₀, t₀, ht₀⟩ := S.exists_stageMap_app_eq hc U s
  refine ⟨j, fun l f hjl ↦ ?_⟩
  obtain rfl : f = f₀ ≫ homOfLE hjl := Subsingleton.elim _ _
  refine ⟨(S.stageTransition f₀ (homOfLE hjl)).hom.app (op U) t₀, ?_⟩
  rw [← ht₀, ← S.stageTransition_stageMap f₀ (homOfLE hjl)]
  rfl

include hc in
/-- Finitely many sections of `Fⱼ` whose images in the sections of `L` vanish are all killed by
a compatible transition to a later stage. -/
lemma exists_stageTransition_app_eq_zero_of_finite {i₀ j : I} {ι : Type*} [Finite ι]
    (W : ι → (D.obj (op i₀)).Etale) [∀ y, CompactSpace (W y).left]
    [∀ y, QuasiSeparatedSpace (W y).left] (f : i₀ ⟶ j)
    (t : ∀ y, (S.stageSheaf f).obj.obj (op (W y)))
    (ht : ∀ y, (S.stageMap f).hom.app (op (W y)) (t y) = 0) :
    ∃ (l : I) (f' : i₀ ⟶ l) (ψ : S.stageSheaf f ⟶ S.stageSheaf f'),
      ψ ≫ S.stageMap f' = S.stageMap f ∧ ∀ y, ψ.hom.app (op (W y)) (t y) = 0 := by
  classical
  have := Fintype.ofFinite ι
  suffices H : ∀ s : Finset ι, ∃ (l : I) (f' : i₀ ⟶ l) (ψ : S.stageSheaf f ⟶ S.stageSheaf f'),
      ψ ≫ S.stageMap f' = S.stageMap f ∧ ∀ y ∈ s, ψ.hom.app (op (W y)) (t y) = 0 by
    obtain ⟨l, f', ψ, hψ, h⟩ := H Finset.univ
    exact ⟨l, f', ψ, hψ, fun y ↦ h y (Finset.mem_univ y)⟩
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨j, f, 𝟙 _, Category.id_comp _, by simp⟩
  | insert a s ha ih =>
    obtain ⟨l, f', ψ, hψ, h⟩ := ih
    have h₀ : (S.stageMap f').hom.app (op (W a)) (ψ.hom.app (op (W a)) (t a)) = 0 := by
      rw [← ht a, ← hψ]
      rfl
    obtain ⟨l', f'', ψ', hψ', h'⟩ := S.exists_stageTransition_app_eq_zero hc (W a) f' _ h₀
    refine ⟨l', f'', ψ ≫ ψ', by rw [Category.assoc, hψ', hψ], fun y hy ↦ ?_⟩
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact h'
    · change ψ'.hom.app _ (ψ.hom.app _ (t y)) = 0
      rw [h y hy, map_zero]

omit [IsDirected I (· ≤ ·)] [Nonempty I] [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
  [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)] [∀ (i j : Iᵒᵖ) (f : i ⟶ j), IsAffineHom (D.map f)]
  in
/-- The stage sheaves of a system of injective sheaves are injective. -/
lemma injective_stageSheaf (hE : ∀ i, Injective (S.F i)) {i₀ j : I} (f : i₀ ⟶ j) :
    Injective (S.stageSheaf f) := by
  have := Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (D.map f.op))
  exact (lowerStar AddCommGrpCat.{u + 1} (D.map f.op)).injective_obj_of_injective (hE j)

include hc in
/-- **Čech complexes of the colimit of a system of injective sheaves.** For a finite family `U₀`
over a stage `D_{i₀}` with quasi-compact quasi-separated Čech nerve, the Čech complex of the
pushforward to `D_{i₀}` of the colimit `L` of a system of injective sheaves is exact in positive
degrees. -/
lemma exactAt_cechComplex_lowerStar_of_injective (hE : ∀ i, Injective (S.F i)) {i₀ : I}
    {V₀ : (D.obj (op i₀)).Etale} {n : ℕ} (U₀ : Fin n → Over V₀)
    (hU : ∀ (m : ℕ) (y : Fin (m + 1) → Fin n), CompactSpace (cechNerveObj U₀ y).left.left ∧
      QuasiSeparatedSpace (cechNerveObj U₀ y).left.left) (q : ℕ) :
    ((cechComplex U₀).obj
      ((lowerStar AddCommGrpCat.{u + 1} (c.π.app (op i₀))).obj S.L.pt).obj).ExactAt (q + 1) := by
  classical
  rw [exactAt_cechComplex_iff]
  intro z hz
  -- the components of `z` come from a common stage `l`
  have hlift (y : Fin (q + 2) → Fin n) := by
    have := (hU _ y).1
    have := (hU _ y).2
    exact S.exists_stageMap_app_eq_of_le hc (cechNerveObj U₀ y).left (z y)
  choose j hj using hlift
  obtain ⟨l, hl⟩ := Finset.exists_le (insert i₀ (Finset.univ.image j))
  let f : i₀ ⟶ l := homOfLE (hl i₀ (Finset.mem_insert_self _ _))
  choose t ht using fun y ↦ hj y l f
    (hl _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ y))))
  let T : ((cechComplex U₀).obj (S.stageSheaf f).obj).X (q + 1) := t
  have hT : ((cechComplex U₀).map (S.stageMap f).hom).f (q + 1) T = z :=
    funext fun y ↦ by rw [cechComplex_map_f_apply]; exact ht y
  -- the coboundary of `T` vanishes at a later stage
  have hdT (y : Fin (q + 3) → Fin n) : (S.stageMap f).hom.app _
      (((cechComplex U₀).obj (S.stageSheaf f).obj).d (q + 1) (q + 2) T y) = 0 := by
    have h := congr_fun (cechComplex_map_f_d_apply U₀ (S.stageMap f).hom (q + 1) T) y
    rw [hT, hz, cechComplex_map_f_apply] at h
    exact h
  have : ∀ y : Fin (q + 3) → Fin n, CompactSpace (cechNerveObj U₀ y).left.left :=
    fun y ↦ (hU _ y).1
  have : ∀ y : Fin (q + 3) → Fin n, QuasiSeparatedSpace (cechNerveObj U₀ y).left.left :=
    fun y ↦ (hU _ y).2
  obtain ⟨l', f', ψ, hψ, hψ₀⟩ := S.exists_stageTransition_app_eq_zero_of_finite hc
    (fun y : Fin (q + 3) → Fin n ↦ (cechNerveObj U₀ y).left) f _ hdT
  -- the image of `T` at the stage `l'` is a cocycle of an injective sheaf
  have := S.injective_stageSheaf hE f'
  obtain ⟨b, hb⟩ := (exactAt_cechComplex_iff U₀ _ q).1
    (Sheaf.exactAt_cechComplex_of_injective (S.stageSheaf f') U₀ q)
    (((cechComplex U₀).map ψ.hom).f (q + 1) T) (by
      rw [← cechComplex_map_f_d_apply]
      funext y
      rw [cechComplex_map_f_apply]
      exact hψ₀ y)
  refine ⟨((cechComplex U₀).map (S.stageMap f').hom).f q b, ?_⟩
  rw [← cechComplex_map_f_d_apply, hb, ← hT, ← ConcreteCategory.comp_apply,
    ← HomologicalComplex.comp_f, ← Functor.map_comp, ← ObjectProperty.FullSubcategory.comp_hom,
    hψ]

variable (c) in
/-- An étale `X`-scheme is a *stage object* if it is the base change of a quasi-compact
quasi-separated étale scheme over some stage `Dₖ`. -/
def IsStageObject (V : c.pt.Etale) : Prop :=
  ∃ (k : I) (V₀ : (D.obj (op k)).Etale), CompactSpace V₀.left ∧ QuasiSeparatedSpace V₀.left ∧
    Nonempty ((c.π.app (op k)).Etale.obj V₀ ≅ V)

variable (c) in
/-- A finite family over an étale `X`-scheme `V` is a *stage family* if it is isomorphic to the
base change of a finite family of affine étale schemes over a quasi-compact quasi-separated
étale scheme over some stage `Dₖ`, whose base change is `V`. -/
def IsStageFamily (V : c.pt.Etale) {n : ℕ} (U : Fin n → Over V) : Prop :=
  ∃ (k : I) (V₀ : (D.obj (op k)).Etale) (_ : CompactSpace V₀.left)
    (_ : QuasiSeparatedSpace V₀.left) (e : (c.π.app (op k)).Etale.obj V₀ ≅ V)
    (U₀ : Fin n → Over V₀), (∀ a, IsAffine (U₀ a).left.left) ∧
      Nonempty (∀ a, U a ≅ (Over.post (c.π.app (op k)).Etale ⋙ Over.map e.hom).obj (U₀ a))

include hc in
/-- The Čech complexes of the colimit of a system of injective sheaves on stage families are
exact in positive degrees. -/
lemma exactAt_cechComplex_of_isStageFamily (hE : ∀ i, Injective (S.F i)) {V : c.pt.Etale}
    {n : ℕ} (U : Fin n → Over V) (hU : IsStageFamily c V U) (q : ℕ) :
    ((cechComplex U).obj S.L.pt.obj).ExactAt (q + 1) := by
  obtain ⟨k, V₀, _, _, e, U₀, hU₀, ⟨ι⟩⟩ := hU
  have : PreservesFiniteProducts (Over.map e.hom) :=
    inferInstanceAs (PreservesFiniteProducts (Over.mapIso e).functor)
  have : PreservesFiniteLimits (Over.post (c.π.app (op k)).Etale) := inferInstance
  have : PreservesFiniteProducts (Over.post (c.π.app (op k)).Etale) := inferInstance
  refine exactAt_cechComplex_of_preservesFiniteProducts
    (Over.post (c.π.app (op k)).Etale ⋙ Over.map e.hom) U₀ U ι
    ((lowerStar AddCommGrpCat.{u + 1} (c.π.app (op k))).obj S.L.pt).obj S.L.pt.obj (Iso.refl _)
    (q + 1) (S.exactAt_cechComplex_lowerStar_of_injective hc hE U₀ (fun m y ↦ ?_) q)
  exact Scheme.compactSpace_and_quasiSeparatedSpace_piObj _ fun l ↦ by
    have := hU₀ (y l)
    exact ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry.Etale.SystemData
