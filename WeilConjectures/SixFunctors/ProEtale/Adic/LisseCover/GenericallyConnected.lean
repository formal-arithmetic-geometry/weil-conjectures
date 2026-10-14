/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.FiniteOrbit
public import WeilConjectures.AlgebraicGeometry.AffineFibreProductTransition
public import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import WeilConjectures.RingTheory.ProEtale.WeaklyEtaleIndEtale
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Generic connectedness of pro-étale schemes over regular schemes

Let `Y` be a regular locally Noetherian scheme with generic point `η`. A limit `W = lim Wᵢ` of
a cofiltered diagram of affine schemes étale over `Y` is generically connected relative to `η`
(`AlgebraicGeometry.IsGenericallyConnected`, `AlgebraicGeometry.isGenericallyConnected_of_isLimit`):
an open neighbourhood of a diagonal point of `W ×_Y W` contains the preimage of an open of some
`Wᵢ ×_Y Wᵢ` (`W ×_Y W` being the limit of the `Wᵢ ×_Y Wᵢ`), the stage `Wᵢ` is regular, hence
locally irreducible, and points of an irreducible open of `Wᵢ` lying over `η` are its generic
point, `Wᵢ ⟶ Y` having discrete fibres.

Every weakly étale `f : V ⟶ Y` with `V` quasi-compact admits a surjective submersive morphism
`j : W ⟶ V` from such a `W`, by Stacks 097Z (a weakly étale algebra is ind-étale locally
ind-étale) (`AlgebraicGeometry.exists_isGenericallyConnected_cover`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace CategoryTheory.Limits

variable {C : Type*} [Category C] [HasPullbacks C] {J : Type*} [Category J] {D : J ⥤ C} {S X : C}
  (t : D ⟶ (Functor.const J).obj S)

/-- The diagram `j ↦ Dⱼ ×_S Dⱼ` of a diagram `D` over `S`. -/
@[simps]
noncomputable def pullbackDiagramSelf : J ⥤ C where
  obj j := pullback (t.app j) (t.app j)
  map u := pullback.map _ _ _ _ (D.map u) (D.map u) (𝟙 S) (by simp) (by simp)
  map_id j := by ext <;> simp
  map_comp u v := by ext <;> simp

variable {t} (s : (Functor.const J).obj X ⟶ D) (h : X ⟶ S) (hh : ∀ j, s.app j ≫ t.app j = h)

/-- The cone `X ×_S X ⟶ Dⱼ ×_S Dⱼ` over `pullbackDiagramSelf t`. -/
@[simps]
noncomputable def pullbackConeSelf : Cone (pullbackDiagramSelf t) where
  pt := pullback h h
  π :=
    { app j := pullback.map h h _ _ (s.app j) (s.app j) (𝟙 S) (by simp [hh]) (by simp [hh])
      naturality u v w := by
        have hw : s.app u ≫ D.map w = s.app v := by simpa using (s.naturality w).symm
        dsimp
        rw [Category.id_comp]
        refine pullback.hom_ext ?_ ?_ <;> simp [hw] }

/-- The cone over `D` given by the first (`b = false`) or second projections of a cone over
`pullbackDiagramSelf t`. -/
@[simps]
noncomputable def coneOfPullbackDiagramSelf (c : Cone (pullbackDiagramSelf t)) (b : Bool) :
    Cone D where
  pt := c.pt
  π :=
    { app j := c.π.app j ≫ if b then pullback.snd _ _ else pullback.fst _ _
      naturality u v w := by
        have := c.π.naturality w
        dsimp at this ⊢
        rw [Category.id_comp] at this
        rw [Category.id_comp, this]
        cases b <;> simp }

/-- **Fibre products commute with limits**: if `X = lim Dⱼ` over `S` (and the index category is
nonempty), then `X ×_S X = lim (Dⱼ ×_S Dⱼ)`. -/
noncomputable def isLimitPullbackConeSelf [Nonempty J] (hs : IsLimit (Cone.mk X s)) :
    IsLimit (pullbackConeSelf s h hh) where
  lift c := pullback.lift (hs.lift (coneOfPullbackDiagramSelf c false))
    (hs.lift (coneOfPullbackDiagramSelf c true)) (by
      obtain ⟨j⟩ := ‹Nonempty J›
      rw [← hh j]
      have h₁ := hs.fac (coneOfPullbackDiagramSelf c false) j
      have h₂ := hs.fac (coneOfPullbackDiagramSelf c true) j
      simp only [coneOfPullbackDiagramSelf_π_app] at h₁ h₂
      simp only [Bool.false_eq_true, ↓reduceIte] at h₁ h₂
      rw [reassoc_of% h₁, reassoc_of% h₂]
      exact c.π.app j ≫= pullback.condition)
  fac c j := by
    refine pullback.hom_ext ?_ ?_
    · have := hs.fac (coneOfPullbackDiagramSelf c false) j
      simp only [coneOfPullbackDiagramSelf_π_app,
        Bool.false_eq_true, ↓reduceIte] at this
      rw [Category.assoc, pullbackConeSelf_π_app, pullback.lift_fst, pullback.lift_fst_assoc, this]
    · have := hs.fac (coneOfPullbackDiagramSelf c true) j
      simp only [coneOfPullbackDiagramSelf_π_app,
        ↓reduceIte] at this
      rw [Category.assoc, pullbackConeSelf_π_app, pullback.lift_snd, pullback.lift_snd_assoc, this]
  uniq c m hm := by
    refine pullback.hom_ext (hs.hom_ext fun j ↦ ?_) (hs.hom_ext fun j ↦ ?_)
    · have h₁ := congrArg (· ≫ pullback.fst _ _) (hm j)
      have h₂ := hs.fac (coneOfPullbackDiagramSelf c false) j
      simp only [coneOfPullbackDiagramSelf_π_app,
        Bool.false_eq_true, ↓reduceIte] at h₂
      simp only [pullbackConeSelf_π_app, Category.assoc,
        pullback.lift_fst] at h₁
      simp only [Category.assoc, pullback.lift_fst_assoc]
      rw [h₁, h₂]
    · have h₁ := congrArg (· ≫ pullback.snd _ _) (hm j)
      have h₂ := hs.fac (coneOfPullbackDiagramSelf c true) j
      simp only [coneOfPullbackDiagramSelf_π_app,
        ↓reduceIte] at h₂
      simp only [pullbackConeSelf_π_app, Category.assoc,
        pullback.lift_snd] at h₁
      simp only [Category.assoc, pullback.lift_snd_assoc]
      rw [h₁, h₂]

end CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A regular locally Noetherian scheme is locally irreducible: every point has an open
neighbourhood consisting of specializations of a single point. Indeed an affine open
neighbourhood is a regular Noetherian scheme, hence a finite disjoint union of open integral
subschemes (`AlgebraicGeometry.IsRegular.exists_isClopen_isIntegral`). -/
lemma IsRegular.exists_isOpen_specializes (X : Scheme.{u}) [IsRegular X] [IsLocallyNoetherian X]
    (x : X) : ∃ (O : Set X) (ξ : X), IsOpen O ∧ x ∈ O ∧ ∀ y ∈ O, ξ ⤳ y := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) trivial
  have : IsAffine U := hU
  have : IsRegular U := ⟨isRegularLocalRing_stalk_of_etale U.ι fun _ ↦ inferInstance⟩
  have : IsNoetherian U := ⟨⟩
  obtain ⟨n, Ua, -, -, hsup, hint⟩ := IsRegular.exists_isClopen_isIntegral U
  have hx : (⟨x, hxU⟩ : U) ∈ ⨆ a, Ua a := by rw [hsup]; trivial
  obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  have := (hint a).1
  refine ⟨U.ι.base '' (Ua a : Set U), U.ι.base ((Ua a).ι.base (genericPoint (Ua a))),
    U.ι.isOpenEmbedding.isOpenMap _ (Ua a).isOpen, ⟨_, ha, rfl⟩, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  let y' : (Ua a).toScheme := ⟨y, hy⟩
  have := ((genericPoint_specializes y').map ((Ua a).ι ≫ U.ι).base.hom.continuous)
  simpa only [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply] using this

/-- **Generic connectedness of pro-étale limits.** Let `h : W ⟶ Y` be a cofiltered limit of
affine schemes `Dⱼ` over `Y` with locally quasi-finite (e.g. étale) structure maps, and assume
every point of every `Dⱼ` has an open neighbourhood consisting of specializations of a single
point (e.g. `Dⱼ` regular). Then `h` is generically connected relative to any point `η` of `Y`
specializing to every point (`AlgebraicGeometry.IsGenericallyConnected`). -/
theorem isGenericallyConnected_of_isLimit {W Y : Scheme.{u}} (h : W ⟶ Y) {J : Type u}
    [SmallCategory J] [IsCofiltered J] {D : J ⥤ Scheme.{u}} {t : D ⟶ (Functor.const J).obj Y}
    {s : (Functor.const J).obj W ⟶ D} (hs : IsLimit (Cone.mk W s))
    (hh : ∀ j, s.app j ≫ t.app j = h) [∀ j, IsAffine (D.obj j)]
    [∀ j, LocallyQuasiFinite (t.app j)]
    (hirr : ∀ j (q : D.obj j), ∃ (O : Set (D.obj j)) (ξ : D.obj j), IsOpen O ∧ q ∈ O ∧
      ∀ y ∈ O, ξ ⤳ y)
    {η : Y} (hη : ∀ y, η ⤳ y) : IsGenericallyConnected h η := by
  intro w Ω hΩ hw
  have : Nonempty J := IsCofiltered.nonempty
  have hlim := isLimitPullbackConeSelf s h hh hs
  have : IsAffineHom (𝟙 Y) := inferInstance
  have : ∀ {i j : J} (u : i ⟶ j), IsAffineHom ((pullbackDiagramSelf t).map u) := fun u ↦
    isAffineHom_pullback_map (t.app _) (t.app _) (t.app _) (t.app _) (D.map u) (𝟙 Y) (D.map u)
      (by simp) (by simp)
  obtain ⟨_, ⟨_, ⟨j, V, -, rfl⟩, rfl⟩, hwV, hVΩ⟩ :=
    (isBasis_preimage_isAffineOpen _ _ hlim).exists_subset_of_mem_open hw hΩ
  set sj : W ⟶ D.obj j := s.app j
  set πj := (pullbackConeSelf s h hh).π.app j
  have hΔ : pullback.diagonal h ≫ πj = sj ≫ pullback.diagonal (t.app j) :=
    pullback.hom_ext (by simp [πj, sj]) (by simp [πj, sj])
  have hwV' : (pullback.diagonal (t.app j)).base (sj.base w) ∈ V := by
    rw [← Scheme.Hom.comp_apply, ← hΔ, Scheme.Hom.comp_apply]
    exact hwV
  obtain ⟨O, ξ, hO, hwO, hξ⟩ := hirr j (sj.base w)
  let V' : Set ↥(pullback (t.app j) (t.app j)) := (V : Set ((pullbackDiagramSelf t).obj j))
  have hV' : IsOpen V' := V.isOpen
  refine ⟨sj.base ⁻¹' (O ∩ (pullback.diagonal (t.app j)).base ⁻¹' V'),
    ((hO.inter (hV'.preimage (pullback.diagonal (t.app j)).base.hom.continuous)).preimage
      sj.base.hom.continuous).mem_nhds ⟨hwO, hwV'⟩, ?_⟩
  rintro w₁ ⟨hw₁O, -⟩ a b ha hb haη hbη
  have htξ (q : D.obj j) (hq : q ∈ O) (hqη : (t.app j).base q = η) : (t.app j).base ξ = η :=
    (((hξ q hq).map (t.app j).base.hom.continuous).antisymm (by rw [hqη]; exact hη _)).eq.trans
      hqη
  have hξq (q : D.obj j) (hq : q ∈ O) (hqη : (t.app j).base q = η) : ξ = q :=
    (t.app j).eq_of_specializes_of_apply_eq (hξ q hq) ((htξ q hq hqη).trans hqη.symm)
  have hsη (c : W) (hc : h.base c = η) : (t.app j).base (sj.base c) = η := by
    rw [← Scheme.Hom.comp_apply, hh]
    exact hc
  have haO : sj.base a ∈ O := (ha.map sj.base.hom.continuous).mem_open hO hw₁O
  have hbO : sj.base b ∈ O := (hb.map sj.base.hom.continuous).mem_open hO hwO
  have haξ := hξq _ haO (hsη a haη)
  have hbξ := hξq _ hbO (hsη b hbη)
  obtain ⟨ρ, hρ₁, hρ₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := sj) (g := sj) a b
    (haξ.symm.trans hbξ)
  let M : pullback sj sj ⟶ pullback h h :=
    pullback.map sj sj h h (𝟙 _) (𝟙 _) (t.app j) (by simp [sj, hh]) (by simp [sj, hh])
  have hM : M ≫ πj = pullback.fst sj sj ≫ sj ≫ pullback.diagonal (t.app j) := by
    refine pullback.hom_ext ?_ ?_
    · simp [M, πj, sj]
    · simp [M, πj, sj, pullback.condition]
  refine ⟨M.base ρ, hVΩ ?_, ?_, ?_⟩
  · show (M ≫ πj).base ρ ∈ V'
    rw [hM, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hρ₁, ← haξ]
    exact ((hξ _ hwO).map (pullback.diagonal (t.app j)).base.hom.continuous).mem_open hV'
      hwV'
  · rw [← Scheme.Hom.comp_apply, pullback.lift_fst, Category.comp_id, hρ₁]
  · rw [← Scheme.Hom.comp_apply, pullback.lift_snd, Category.comp_id, hρ₂]

end AlgebraicGeometry
