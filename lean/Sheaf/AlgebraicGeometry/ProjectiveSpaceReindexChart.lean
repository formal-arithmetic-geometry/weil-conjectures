/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfInvertible
import WeilConjectures.Blowup.FiniteDegree.ChartProbe

/-! # Coordinate reindexing on a standard projective chart

Source: Stacks Project, Constructions, Definition 01NF and Lemma 01NE.
(blueprint: lem-weil-pbc-projective-space-reindex-chart).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProjectiveSpace

set_option backward.isDefEq.respectTransparency false

private lemma normalized_homOfSections {X S : Scheme.{u}} {n : Type u}
    (g : X ⟶ S) (s : n → Γ(X, ⊤)) (hs : Ideal.span (Set.range s) = ⊤)
    (i : n) (hsi : s i = 1) :
    homOfSections g s hs =
      AffineSpace.homOfVector g (fun j : {j : n // j ≠ i} ↦ s j.1) ≫
        (standardOpenIso n S i).inv ≫ (standardOpen n S i).ι := by
  let B := X.basicOpen (s i)
  have hB : B = ⊤ := by rw [show B = X.basicOpen (s i) from rfl, hsi, X.basicOpen_one]
  have hle := (homOfSections_preimage_standardOpen g s hs i).ge
  have : IsIso B.ι := by
    rw [← X.isoOfEq_hom_ι hB, ← Scheme.topIso_hom]
    infer_instance
  have hres : (homOfSections g s hs).resLE (standardOpen n S i) B hle ≫
      (standardOpenIso n S i).hom =
      B.ι ≫ AffineSpace.homOfVector g (fun j : {j : n // j ≠ i} ↦ s j.1) := by
    rw [homOfSections_resLE_standardOpenIso_hom]
    apply AffineSpace.hom_ext
    · simp [B]
    · intro j
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        AffineSpace.homOfVector_appTop_coord, AffineSpace.homOfVector_appTop_coord]
      symm
      apply X.eq_divBasicOpen
      have h1 : (X.basicOpen (s i)).ι.appTop (s i) = 1 := by
        rw [hsi, map_one]
      rw [h1, mul_one]
  apply (cancel_epi B.ι).mp
  rw [← Scheme.Hom.resLE_comp_ι _ hle]
  have hres' : (homOfSections g s hs).resLE (standardOpen n S i) B hle =
      B.ι ≫ AffineSpace.homOfVector g (fun j : {j : n // j ≠ i} ↦ s j.1) ≫
        (standardOpenIso n S i).inv := by
    apply (cancel_mono (standardOpenIso n S i).hom).mp
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hres
  rw [hres']
  simp only [Category.assoc]

private lemma chart_coord {n : Type u} (S : Scheme.{u}) (i : n)
    (j : {j : n // j ≠ i}) :
    (standardOpenIso n S i).hom.appTop (AffineSpace.coord S j) =
      (standardOpen n S i).topIso.inv (coordRatio n S i j.1) := by
  classical
  let Y := 𝔸({j : n // j ≠ i}; S)
  let w : n → Γ(Y, ⊤) := fun a ↦ if h : a = i then 1 else AffineSpace.coord S ⟨a, h⟩
  have hwi : w i = 1 := dif_pos rfl
  have hwj (j : {j : n // j ≠ i}) : w j.1 = AffineSpace.coord S j := dif_neg j.2
  have hw : Ideal.span (Set.range w) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i, rfl⟩)
      (by rw [hwi]; exact isUnit_one)
  have hH : homOfSections (Y ↘ S) w hw =
      (standardOpenIso n S i).inv ≫ (standardOpen n S i).ι := by
    rw [normalized_homOfSections _ w hw i hwi]
    have hh : AffineSpace.homOfVector (Y ↘ S)
        (fun j : {j : n // j ≠ i} ↦ w j.1) = 𝟙 Y := by
      apply AffineSpace.hom_ext
      · simp
      · intro j
        rw [AffineSpace.homOfVector_appTop_coord, hwj,
          Scheme.Hom.id_appTop, CommRingCat.id_apply]
    rw [hh, Category.id_comp]
  have hpre : ((standardOpenIso n S i).inv ≫ (standardOpen n S i).ι) ⁻¹ᵁ
      standardOpen n S i = ⊤ := by simp
  have hh := homOfSections_appLE_coordRatio (Y ↘ S) w hw hwi j.1 (hH.symm ▸ hpre.ge)
  rw [Scheme.Hom.appLE_eq_of_eq hH, hwj] at hh
  have hh' : (standardOpenIso n S i).inv.appTop
      ((standardOpen n S i).topIso.inv (coordRatio n S i j.1)) =
      AffineSpace.coord S j := by
    have he : (standardOpen n S i).ι.appLE (standardOpen n S i) ⊤
        (standardOpen n S i).ι_preimage_self.ge = (standardOpen n S i).topIso.inv := by
      rw [Scheme.Opens.ι_appLE]
      rfl
    rw [← he, ← CommRingCat.comp_apply, Scheme.Hom.appTop,
      Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    exact hh
  rw [← hh', ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    Iso.hom_inv_id, Scheme.Hom.id_appTop, CommRingCat.id_apply]

/-- On each standard chart, reordering homogeneous sections reorders the affine variables.

Source: Stacks Project, Constructions, Definition 01NF and Lemma 01NE.
(blueprint: lem-weil-pbc-projective-space-reindex-chart).

Proof: Restrict the construction to the open D_+(T_(b i)), using
ι_homOfIsFreeGenerator. The transition formula for the identity pullback of the
coordinate sections gives s_j = (T_(b j)/T_(b i)) s_i. Uniqueness of coefficients
with respect to a free generator identifies sectionRatio i j with this ratio.
The standard chart isomorphism identifies these ratios with affine coordinates,
so localHom is the displayed affine reindexing followed by the target chart inclusion.
The normalized homOfSections computation rule factors the local map through the
standard chart isomorphism. To identify the chart coordinates, apply that same rule
to the family with coordinate 1 at i and affine coordinates elsewhere; its morphism
is the inverse chart inclusion. The native ratio formula then shows that the chart
isomorphism pulls each affine coordinate back to its coordinate ratio. The base maps
agree by homOfSections_over and standardOpenIso_hom_over, and all coordinates agree
by this calculation. AffineSpace.hom_ext proves equality over arbitrary S directly.
For an empty coordinate type there is no i, and the statement is vacuous. -/
theorem ι_homOfIsFreeGenerator_reindex (β γ : Type u) (b : γ ≃ β)
    (S : Scheme.{u}) :
    let s : γ → Γ((Scheme.Modules.pullback (𝟙 ℙ(β; S))).obj (twist β S 1), ⊤) :=
    fun j : γ ↦ Scheme.Modules.pullbackSection (𝟙 ℙ(β; S))
      (twistOneSection β S (b j))
    let U := fun j : γ ↦ standardOpen β S (b j)
    let hs := fun j : γ ↦
      isFreeGenerator_pullbackSection_twistOneSection (𝟙 ℙ(β; S)) (b j)
    let hU : ⨆ j, U j = ⊤ := (b.iSup_comp).trans (iSup_standardOpen β S)
    ∀ (i : γ) (k : β) (h : b i = k), (standardOpen β S k).ι ≫
      homOfIsFreeGenerator s U hs (ℙ(β; S) ↘ S) hU =
        (standardOpenIso β S k).hom ≫
          AffineSpace.reindex
            (fun j : {j : γ // j ≠ i} ↦
              (⟨b j.1, fun he ↦ j.2 (b.injective (he.trans h.symm))⟩ : {j : β // j ≠ k})) S ≫
          (standardOpenIso γ S i).inv ≫ (standardOpen γ S i).ι := by
  dsimp only
  intro i k h
  subst k
  let s : γ → Γ((Scheme.Modules.pullback (𝟙 ℙ(β; S))).obj (twist β S 1), ⊤) :=
    fun j : γ ↦ Scheme.Modules.pullbackSection (𝟙 ℙ(β; S))
    (twistOneSection β S (b j))
  let U := fun j : γ ↦ standardOpen β S (b j)
  let hs := fun j : γ ↦
    isFreeGenerator_pullbackSection_twistOneSection (𝟙 ℙ(β; S)) (b j)
  have hr (j : γ) : sectionRatio s U hs i j = coordRatio β S (b i) (b j) := by
    apply (hs i).coeff_eq_iff _ _ |>.mpr
    symm
    have ht := pullbackSection_twistOneSection_map_eq_smul (𝟙 ℙ(β; S)) (b j) (b i)
    rw [Scheme.Hom.id_app] at ht
    exact ht
  rw [ι_homOfIsFreeGenerator (s := s) (U := U) (hs := hs), localHom,
    normalized_homOfSections _ _ _ i (by simp [localSections])]
  suffices hc : AffineSpace.homOfVector ((U i).ι ≫ ℙ(β; S) ↘ S)
      (fun j : {j : γ // j ≠ i} ↦ localSections s U hs i j.1) =
      (standardOpenIso β S (b i)).hom ≫
        AffineSpace.reindex
          (fun j : {j : γ // j ≠ i} ↦
            (⟨b j.1, fun he ↦ j.2 (b.injective (he.trans rfl))⟩ :
              {j : β // j ≠ b i})) S by
    rw [hc]
    simp only [Category.assoc]
  apply AffineSpace.hom_ext
  · simp [U]
  · intro j
    rw [AffineSpace.homOfVector_appTop_coord, Scheme.Hom.comp_appTop,
      CommRingCat.comp_apply, AffineSpace.reindex_appTop_coord, chart_coord]
    simp only [localSections, hr]
    rfl


end AlgebraicGeometry.ProjectiveSpace
