/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Charts
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.CoordinateCover
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfInvertible

/-!
# The coordinate hyperplane of projective space

The hyperplane `V(T_∗) ⊆ ℙ(Option n; S)` where the extra homogeneous coordinate `T_∗` vanishes
is the image of the *hyperplane embedding* `ℙ(n; S) ⟶ ℙ(Option n; S)`,
`[Tᵢ] ↦ [Tᵢ : 0]` (`AlgebraicGeometry.ProjectiveSpace.hyperplane`), defined by the coordinate
sections of the standard coordinate cover of `ℙ(n; S)` and the zero section. The preimage of the
standard open `D₊(Tᵢ)` is `D₊(Tᵢ)`, and that of `D₊(T_∗)` is empty.

## Main definitions

- `AlgebraicGeometry.ProjectiveSpace.standardCoordinateCover`: the coordinate cover of `ℙ(n; S)`
  by the standard opens.
- `AlgebraicGeometry.ProjectiveSpace.hyperplane`: the hyperplane embedding.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable (n : Type u) (S : Scheme.{u})

/-- The coordinate cover of `ℙ(n; S)` by its standard opens `D₊(Tᵢ)`, with ratios `Tⱼ / Tᵢ`. -/
noncomputable def standardCoordinateCover : ℙ(n; S).CoordinateCover n :=
  Scheme.CoordinateCover.ofProj _ (toProjInt n S) one_pos MvPolynomial.X
    (fun i ↦ MvPolynomial.X_mem_homogeneousSubmodule_one _ i) (iSup_standardOpen n S)

@[simp]
lemma standardCoordinateCover_U (i : n) :
    (standardCoordinateCover n S).U i = standardOpen n S i := rfl

/-- The zero section of degree one of a coordinate cover. -/
def _root_.AlgebraicGeometry.Scheme.CoordinateCover.zeroSection {X : Scheme.{u}} {ι : Type u}
    (𝒟 : X.CoordinateCover ι) : 𝒟.Section 1 where
  s _ := 0
  s_eq _ _ := by simp

/-- The sections defining the hyperplane embedding: the coordinates `Tᵢ`, and `0` for the extra
coordinate. -/
noncomputable def hyperplaneSections : Option n → (standardCoordinateCover n S).Section 1
  | none => (standardCoordinateCover n S).zeroSection
  | some i => (standardCoordinateCover n S).coord i

lemma span_hyperplaneSections (i : n) :
    Ideal.span (Set.range fun a ↦ (hyperplaneSections n S a).s i) = ⊤ := by
  refine Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨some i, rfl⟩) ?_
  simp [hyperplaneSections, (standardCoordinateCover n S).ratio_self i]

/-- **The hyperplane embedding** `ℙ(n; S) ⟶ ℙ(Option n; S)`, `[Tᵢ] ↦ [Tᵢ : 0]`, onto the
hyperplane where the extra coordinate vanishes. -/
noncomputable def hyperplane : ℙ(n; S) ⟶ ℙ(Option n; S) :=
  Scheme.CoordinateCover.hom (hyperplaneSections n S) (span_hyperplaneSections n S)
    (ℙ(n; S) ↘ S)

@[reassoc (attr := simp)]
lemma hyperplane_over : hyperplane n S ≫ ℙ(Option n; S) ↘ S = ℙ(n; S) ↘ S :=
  Scheme.CoordinateCover.hom_over _ _ _

lemma nonvanishing_coord {X : Scheme.{u}} {ι : Type u} (𝒟 : X.CoordinateCover ι) (i : ι) :
    (𝒟.coord i).nonvanishing = 𝒟.U i := by
  refine le_antisymm (iSup_le fun j ↦ ?_) (le_iSup_of_le i ?_)
  · rw [Scheme.CoordinateCover.coord_s, 𝒟.basicOpen_ratio]
    exact inf_le_right
  · rw [Scheme.CoordinateCover.coord_s, 𝒟.ratio_self, Scheme.basicOpen_of_isUnit _ isUnit_one]

/-- The preimage of `D₊(Tᵢ)` under the hyperplane embedding is `D₊(Tᵢ)`. -/
lemma hyperplane_preimage_standardOpen_some (i : n) :
    hyperplane n S ⁻¹ᵁ standardOpen (Option n) S (some i) = standardOpen n S i := by
  rw [hyperplane, Scheme.CoordinateCover.preimage_hom_standardOpen]
  exact nonvanishing_coord _ i

/-- The hyperplane misses `D₊(T_∗)`. -/
lemma hyperplane_preimage_standardOpen_none :
    hyperplane n S ⁻¹ᵁ standardOpen (Option n) S none = ⊥ := by
  rw [hyperplane, Scheme.CoordinateCover.preimage_hom_standardOpen]
  refine le_bot_iff.mp (iSup_le fun j ↦ ?_)
  simp [hyperplaneSections, Scheme.CoordinateCover.zeroSection]
lemma standardCoordinateCover_ratio (i k : n) :
    (standardCoordinateCover n S).ratio i k = coordRatio n S i k := rfl

section Charts

variable {n S}

lemma appLE_eq_of_eq {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (U V e) :
    f.appLE U V e = g.appLE U V (h ▸ e) := by
  subst h
  rfl

/-- A morphism given by sections whose `i`-th member is `1` factors through the chart
`D₊(Tᵢ) ≅ 𝔸({j // j ≠ i}; S)`, with affine coordinates the other sections. -/
lemma homOfSections_eq_of_eq_one {X : Scheme.{u}} (g : X ⟶ S) (s : n → Γ(X, ⊤))
    (hs : Ideal.span (Set.range s) = ⊤) (i : n) (hsi : s i = 1) :
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

/-- The affine coordinates of the chart `D₊(Tᵢ) ≅ 𝔸({j // j ≠ i}; S)` are the ratios
`Tⱼ / Tᵢ`. -/
lemma standardOpenIso_hom_appTop_coord (i : n) (j : {j : n // j ≠ i}) :
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
    rw [homOfSections_eq_of_eq_one _ w hw i hwi]
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
  rw [appLE_eq_of_eq hH, hwj] at hh
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

end Charts
/-! ### The hyperplane embedding is a closed immersion -/

lemma hyperplaneSections_some_s_self (i : n) :
    (standardOpen n S i).topIso.inv ((hyperplaneSections n S (some i)).s i) = 1 := by
  simp [hyperplaneSections, (standardCoordinateCover n S).ratio_self i]

/-- On the standard open `D₊(Tᵢ)`, the hyperplane embedding is, in the charts, the linear map
`𝔸({k // k ≠ i}; S) ⟶ 𝔸({j : Option n // j ≠ some i}; S)` adding the coordinate `0`. -/
lemma ι_hyperplane (i : n) :
    (standardOpen n S i).ι ≫ hyperplane n S =
      AffineSpace.homOfVector ((standardOpen n S i).ι ≫ ℙ(n; S) ↘ S)
          (fun j : {j : Option n // j ≠ some i} ↦
            (standardOpen n S i).topIso.inv ((hyperplaneSections n S j.1).s i)) ≫
        (standardOpenIso (Option n) S (some i)).inv ≫
          (standardOpen (Option n) S (some i)).ι := by
  have h := Scheme.CoordinateCover.ι_hom (𝒟 := standardCoordinateCover n S)
    (hyperplaneSections n S) (span_hyperplaneSections n S) (ℙ(n; S) ↘ S) i
  rw [Scheme.CoordinateCover.localHom,
    homOfSections_eq_of_eq_one _ _ _ (some i) (hyperplaneSections_some_s_self n S i)] at h
  exact h

/-- The hyperplane embedding in the charts over `D₊(Tᵢ)`. -/
noncomputable def hyperplaneChart (i : n) :
    𝔸({k : n // k ≠ i}; S) ⟶ 𝔸({j : Option n // j ≠ some i}; S) :=
  (standardOpenIso n S i).inv ≫
    AffineSpace.homOfVector ((standardOpen n S i).ι ≫ ℙ(n; S) ↘ S)
      (fun j : {j : Option n // j ≠ some i} ↦
        (standardOpen n S i).topIso.inv ((hyperplaneSections n S j.1).s i))

/-- Forgetting the extra coordinate is a retraction of the chart of the hyperplane embedding. -/
lemma hyperplaneChart_comp_reindex (i : n) :
    hyperplaneChart n S i ≫ AffineSpace.reindex
      (fun k : {k : n // k ≠ i} ↦ (⟨some k.1, by simpa using k.2⟩ : {j : Option n // j ≠ some i}))
      S = 𝟙 _ := by
  refine AffineSpace.hom_ext ?_ fun k ↦ ?_
  · rw [Category.assoc, AffineSpace.reindex_over, hyperplaneChart, Category.assoc,
      AffineSpace.homOfVector_over, standardOpenIso_inv_ι_over, Category.id_comp]
  · rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineSpace.reindex_appTop_coord,
      hyperplaneChart, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      AffineSpace.homOfVector_appTop_coord, Scheme.Hom.id_appTop, CommRingCat.id_apply]
    change (standardOpenIso n S i).inv.appTop
      ((standardOpen n S i).topIso.inv (coordRatio n S i k.1)) = _
    rw [← standardOpenIso_hom_appTop_coord, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
      Iso.inv_hom_id, Scheme.Hom.id_appTop, CommRingCat.id_apply]

instance isClosedImmersion_hyperplaneChart (i : n) :
    IsClosedImmersion (hyperplaneChart n S i) := by
  let r := AffineSpace.reindex
    (fun k : {k : n // k ≠ i} ↦ (⟨some k.1, by simpa using k.2⟩ : {j : Option n // j ≠ some i})) S
  have : IsClosedImmersion (hyperplaneChart n S i ≫ r) := by
    rw [hyperplaneChart_comp_reindex]
    infer_instance
  have : IsSeparated (r ≫ 𝔸({k : n // k ≠ i}; S) ↘ S) := by
    rw [AffineSpace.reindex_over]
    infer_instance
  have : IsSeparated r := IsSeparated.of_comp r (𝔸({k : n // k ≠ i}; S) ↘ S)
  exact IsClosedImmersion.of_comp _ r

/-- The preimage of `D₊(Tᵢ)` under the hyperplane embedding, through the chart. -/
noncomputable def hyperplanePreimageIso (i : n) :
    𝔸({k : n // k ≠ i}; S) ≅ (hyperplane n S ⁻¹ᵁ standardOpen (Option n) S (some i)) :=
  (standardOpenIso n S i).symm ≪≫
    ℙ(n; S).isoOfEq (hyperplane_preimage_standardOpen_some n S i).symm

lemma hyperplanePreimageIso_hom_morphismRestrict (i : n) :
    (hyperplanePreimageIso n S i).hom ≫ hyperplane n S ∣_ standardOpen (Option n) S (some i) =
      hyperplaneChart n S i ≫ (standardOpenIso (Option n) S (some i)).inv := by
  rw [← cancel_mono (standardOpen (Option n) S (some i)).ι, Category.assoc,
    morphismRestrict_ι, hyperplaneChart, Category.assoc, Category.assoc, ← ι_hyperplane]
  simp [hyperplanePreimageIso]

/-- **The hyperplane embedding is a closed immersion.** -/
instance isClosedImmersion_hyperplane : IsClosedImmersion (hyperplane n S) := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsClosedImmersion)
    (standardOpen (Option n) S) (iSup_standardOpen _ _) fun a ↦ ?_
  cases a with
  | none =>
    have : IsEmpty (hyperplane n S ⁻¹ᵁ standardOpen (Option n) S none).toScheme :=
      ⟨fun x ↦ by
        have h : x.1 ∈ (⊥ : ℙ(n; S).Opens) := by
          rw [← hyperplane_preimage_standardOpen_none n S]
          exact x.2
        exact h⟩
    infer_instance
  | some i =>
    let e : 𝔸({k : n // k ≠ i}; S) ≅ (hyperplane n S ⁻¹ᵁ standardOpen (Option n) S (some i)) :=
      (standardOpenIso n S i).symm ≪≫
        ℙ(n; S).isoOfEq (hyperplane_preimage_standardOpen_some n S i).symm
    have he : e.hom ≫ hyperplane n S ∣_ standardOpen (Option n) S (some i) =
        hyperplaneChart n S i ≫ (standardOpenIso (Option n) S (some i)).inv := by
      rw [← cancel_mono (standardOpen (Option n) S (some i)).ι, Category.assoc,
        morphismRestrict_ι, hyperplaneChart, Category.assoc, Category.assoc, ← ι_hyperplane]
      simp [e]
    rw [← MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion) e.hom, he]
    infer_instance
/-! ### The hyperplane is the zero locus of `T_∗ / Tᵢ` on `D₊(Tᵢ)` -/

/-- The extra affine coordinate `T_∗ / Tᵢ` of the chart `D₊(Tᵢ)` of `ℙ(Option n; S)`. -/
noncomputable abbrev extraCoord (i : n) : Γ(𝔸({j : Option n // j ≠ some i}; S), ⊤) :=
  AffineSpace.coord S ⟨none, by simp⟩

lemma hyperplaneChart_appTop_extraCoord (i : n) :
    (hyperplaneChart n S i).appTop (extraCoord n S i) = 0 := by
  rw [hyperplaneChart, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    AffineSpace.homOfVector_appTop_coord]
  simp [hyperplaneSections, Scheme.CoordinateCover.zeroSection]

lemma hyperplaneChart_appTop_coord_some (i : n) (k : {k : n // k ≠ i}) :
    (hyperplaneChart n S i).appTop (AffineSpace.coord S ⟨some k.1, by simpa using k.2⟩) =
      AffineSpace.coord S k := by
  have h := congrArg (fun φ : 𝔸({k : n // k ≠ i}; S) ⟶ 𝔸({k : n // k ≠ i}; S) ↦
    φ.appTop (AffineSpace.coord S k)) (hyperplaneChart_comp_reindex n S i)
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineSpace.reindex_appTop_coord,
    Scheme.Hom.id_appTop, CommRingCat.id_apply] at h
  exact h

@[reassoc (attr := simp)]
lemma hyperplaneChart_over (i : n) :
    hyperplaneChart n S i ≫ 𝔸({j : Option n // j ≠ some i}; S) ↘ S =
      𝔸({k : n // k ≠ i}; S) ↘ S := by
  rw [hyperplaneChart, Category.assoc, AffineSpace.homOfVector_over, standardOpenIso_inv_ι_over]

/-- The chart of the hyperplane embedding is the closed subscheme `V(T_∗ / Tᵢ)`. -/
noncomputable def hyperplaneChartIso (i : n) :
    𝔸({k : n // k ≠ i}; S) ≅
      𝔸({j : Option n // j ≠ some i}; S).zeroLocusSubscheme {extraCoord n S i} where
  hom := (hyperplaneChart n S i).liftZeroLocusSubscheme (by
    rintro _ rfl
    exact hyperplaneChart_appTop_extraCoord n S i)
  inv := 𝔸({j : Option n // j ≠ some i}; S).zeroLocusSubschemeι {extraCoord n S i} ≫
    AffineSpace.reindex
      (fun k : {k : n // k ≠ i} ↦ (⟨some k.1, by simpa using k.2⟩ : {j : Option n // j ≠ some i}))
      S
  hom_inv_id := by
    rw [Scheme.Hom.liftZeroLocusSubscheme_zeroLocusSubschemeι_assoc,
      hyperplaneChart_comp_reindex]
  inv_hom_id := by
    rw [← cancel_mono (𝔸({j : Option n // j ≠ some i}; S).zeroLocusSubschemeι
      {extraCoord n S i}), Category.assoc, Category.assoc,
      Scheme.Hom.liftZeroLocusSubscheme_zeroLocusSubschemeι, Category.id_comp]
    refine AffineSpace.hom_ext ?_ fun ⟨j, hj⟩ ↦ ?_
    · simp [AffineSpace.reindex_over]
    · cases j with
      | none =>
        rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, Scheme.Hom.comp_appTop,
          CommRingCat.comp_apply, hyperplaneChart_appTop_extraCoord, map_zero, map_zero]
        exact (Scheme.zeroLocusSubschemeι_appTop (Set.mem_singleton _)).symm
      | some k =>
        rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, Scheme.Hom.comp_appTop,
          CommRingCat.comp_apply,
          hyperplaneChart_appTop_coord_some n S i ⟨k, fun h ↦ hj (by rw [h])⟩,
          AffineSpace.reindex_appTop_coord]

@[reassoc (attr := simp)]
lemma hyperplaneChartIso_hom_ι (i : n) :
    (hyperplaneChartIso n S i).hom ≫
      𝔸({j : Option n // j ≠ some i}; S).zeroLocusSubschemeι {extraCoord n S i} =
      hyperplaneChart n S i := by
  simp [hyperplaneChartIso]

end AlgebraicGeometry.ProjectiveSpace
