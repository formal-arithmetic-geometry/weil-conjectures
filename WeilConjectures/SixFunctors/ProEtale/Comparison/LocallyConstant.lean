/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
public import WeilConjectures.SixFunctors.ProEtale.Comparison.EssImage

/-!
# Pro-étale locally constant sheaves of étale origin

-/

@[expose] public section

universe w v u v' u'

open CategoryTheory Limits Opposite

namespace CategoryTheory

section Pushforward

variable {C' : Type*} [Category* C'] {C : Type*} [Category* C] (H : C' ⥤ C)
  (J' : GrothendieckTopology C') (J : GrothendieckTopology C) [H.IsContinuous J' J]
  (A : Type u') [Category.{v'} A] [HasWeakSheafify J A] [HasWeakSheafify J' A]
  {T' : C'} (hT' : IsTerminal T')

/-- The canonical map from the constant sheaf at `M` on `(C', J')` to the restriction along a
continuous functor `H : C' ⥤ C` of the constant sheaf at `M` on `(C, J)`, adjoint to
`M ⟶ M_C(H T')` for a terminal object `T'` of `C'`. -/
noncomputable def constantSheafPushforwardHom (M : A) :
    (constantSheaf J' A).obj M ⟶ (H.sheafPushforwardContinuous A J' J).obj
      ((constantSheaf J A).obj M) :=
  ((constantSheafAdj J' A hT').homEquiv M _).symm
    ((CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op (H.obj T')))

/-- The canonical map is compatible with the sheafification maps of the constant presheaves. -/
lemma toSheafify_constantSheafPushforwardHom_hom (M : A) :
    CategoryTheory.toSheafify J' ((Functor.const C'ᵒᵖ).obj M) ≫
        (constantSheafPushforwardHom H J' J A hT' M).hom =
      Functor.whiskerLeft H.op
        (CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj M)) := by
  apply ((constantPresheafAdj A hT').homEquiv M _).injective
  have h : (constantSheafAdj J' A hT').homEquiv M _ (constantSheafPushforwardHom H J' J A hT' M) =
      (CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op (H.obj T')) :=
    Equiv.apply_symm_apply _ _
  rw [constantSheafAdj_homEquiv_apply] at h
  simp only [Adjunction.homEquiv_unit, constantPresheafAdj_unit_app, evaluation_obj_map,
    Category.id_comp, NatTrans.comp_app, Functor.whiskerLeft_app]
  exact h

variable {FA : A → A → Type*} {CA : A → Type*}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
  [J.WEqualsLocallyBijective A] [J'.WEqualsLocallyBijective A]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [J'.HasSheafCompose (CategoryTheory.forget A)] [H.IsCocontinuous J' J]

include FA CA in
/-- **The restriction of a constant sheaf along a continuous and cocontinuous functor is the
constant sheaf**, through the canonical map. -/
instance isIso_constantSheafPushforwardHom (M : A) :
    IsIso (constantSheafPushforwardHom H J' J A hT' M) := by
  rw [← Sheaf.isLocallyBijective_iff_isIso (constantSheafPushforwardHom H J' J A hT' M)]
  have h := toSheafify_constantSheafPushforwardHom_hom H J' J A hT' M
  have h₁ : Presheaf.IsLocallyInjective J' (Functor.whiskerLeft H.op
      (CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj M))) :=
    Presheaf.isLocallyInjective_whisker J' J H _
  have h₂ : Presheaf.IsLocallySurjective J' (Functor.whiskerLeft H.op
      (CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj M))) :=
    Presheaf.isLocallySurjective_whisker J' J H _
  rw [← h] at h₁ h₂
  have h₃ : Presheaf.IsLocallyInjective J'
      (CategoryTheory.toSheafify J' ((Functor.const C'ᵒᵖ).obj M)) :=
    (J'.W_toSheafify _).isLocallyInjective
  have h₄ : Presheaf.IsLocallySurjective J'
      (CategoryTheory.toSheafify J' ((Functor.const C'ᵒᵖ).obj M)) :=
    (J'.W_toSheafify _).isLocallySurjective
  exact ⟨(Presheaf.comp_isLocallyInjective_iff _ _ _).mp h₁,
    (Presheaf.comp_isLocallySurjective_iff _ _ _).mp h₂⟩

end Pushforward

end CategoryTheory

namespace ModuleCat

/-- **Linear maps out of a finite module lift through filtered colimits**, over a finite ring:
a linear map `t : M ⟶ c.pt` from a finite module `M` to a filtered colimit factors through one
of the stages. Representatives of the finitely many values `t m` live at a common stage, and
the finitely many linearity relations, which hold in the colimit, hold at a later stage. -/
theorem exists_comp_ι_eq_of_isColimit {R : Type u} [Ring R] [Finite R] {J : Type*}
    [Category* J] [IsFiltered J] {K : J ⥤ ModuleCat.{v} R} {c : Cocone K} (hc : IsColimit c)
    [PreservesColimit K (CategoryTheory.forget (ModuleCat.{v} R))]
    {M : ModuleCat.{v} R} [Finite M] (t : M ⟶ c.pt) :
    ∃ (j : J) (s : M ⟶ K.obj j), s ≫ c.ι.app j = t := by
  classical
  have := Fintype.ofFinite M
  have := Fintype.ofFinite R
  let ι (i : J) : K.obj i ⟶ c.pt := c.ι.app i
  have hw {i i' : J} (f : i ⟶ i') (y : K.obj i) :
      (ι i').hom ((K.map f).hom y) = (ι i).hom y :=
    congrArg (fun g ↦ g.hom y) (c.w f)
  choose j x hx using fun m : M ↦ Concrete.isColimit_exists_rep K hc (t m)
  replace hx (m : M) : (ι (j m)).hom (x m) = t.hom m := hx m
  let j₀ := IsFiltered.sup (Finset.univ.image j) ∅
  let s₀ (m : M) : K.obj j₀ := (K.map (IsFiltered.toSup _ ∅ (by simp))).hom (x m)
  have hs₀ (m : M) : (ι j₀).hom (s₀ m) = t.hom m := (hw _ (x m)).trans (hx m)
  let d : (M × M) ⊕ (R × M) → K.obj j₀ := fun
    | .inl p => s₀ (p.1 + p.2) - s₀ p.1 - s₀ p.2
    | .inr p => s₀ (p.1 • p.2) - p.1 • s₀ p.2
  have hd (a) : (ι j₀).hom (d a) = (ι j₀).hom 0 := by
    rcases a with ⟨m, m'⟩ | ⟨r, m⟩ <;> simp [d, hs₀, map_add, map_sub, map_smul]
  have hk (a) : ∃ (k : J) (φ : j₀ ⟶ k), (K.map φ).hom (d a) = 0 := by
    obtain ⟨k, f, g, h⟩ := Concrete.isColimit_exists_of_rep_eq K hc (d a) 0 (hd a)
    refine ⟨k, f, ?_⟩
    have h' : (K.map f).hom (d a) = (K.map g).hom 0 := h
    rw [h', map_zero]
  choose k φ hφ using hk
  let O : Finset J := insert j₀ (Finset.univ.image k)
  let H : Finset (Σ' (X Y : J) (_ : X ∈ O) (_ : Y ∈ O), X ⟶ Y) :=
    Finset.univ.image fun a ↦ ⟨j₀, k a, by simp [O], by simp [O], φ a⟩
  let ψ : j₀ ⟶ IsFiltered.sup O H := IsFiltered.toSup O H (by simp [O])
  have hψ (a) : (K.map ψ).hom (d a) = 0 := by
    have h := IsFiltered.toSup_commutes O H (f := φ a) (by simp [O]) (by simp [O])
      (Finset.mem_image_of_mem _ (Finset.mem_univ a))
    change (K.map (IsFiltered.toSup O H _)).hom (d a) = 0
    rw [← h, Functor.map_comp, hom_comp, LinearMap.comp_apply, hφ, map_zero]
  refine ⟨IsFiltered.sup O H, ModuleCat.ofHom
    { toFun := fun m ↦ (K.map ψ).hom (s₀ m)
      map_add' := fun m m' ↦ ?_
      map_smul' := fun r m ↦ ?_ }, ?_⟩
  · have h := hψ (.inl (m, m'))
    simp only [d, map_sub] at h
    rw [← sub_eq_zero, ← sub_sub]
    exact h
  · have h := hψ (.inr (r, m))
    simp only [d, map_sub, map_smul] at h
    rw [← sub_eq_zero]
    exact h
  · ext m
    exact (hw ψ (s₀ m)).trans (hs₀ m)

end ModuleCat
