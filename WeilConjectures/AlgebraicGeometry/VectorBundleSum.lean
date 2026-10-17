/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorBundle

/-!
# Direct sums of vector bundles

For vector bundles `π : V ⟶ S` of rank `d` and `ρ : W ⟶ S` of rank `e`, the fibre product
`V ×_S W ⟶ S` is a vector bundle of rank `d + e`, the *direct sum*
(`AlgebraicGeometry.VectorBundle.sum`): over the intersection `U i ⊓ U' j` of trivialising opens
its chart has the coordinates of the chart of `V` followed by those of the chart of `W`.

## Main definitions

- `AlgebraicGeometry.VectorBundle.chartRestrict`: a chart restricted to a smaller open.
- `AlgebraicGeometry.VectorBundle.sum`: the direct sum.

## Main statements

- `AlgebraicGeometry.AffineSpace.isPullback_reindex_add`: `𝔸^{d+e}_S = 𝔸^d_S ×_S 𝔸^e_S`.
- `AlgebraicGeometry.VectorBundle.sum_coord`: the coordinates of the direct sum.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace AffineSpace

variable (S : Scheme.{u}) (d e : ℕ)

/-- The first `d` coordinates `𝔸^{d+e}_S ⟶ 𝔸^d_S`. -/
noncomputable abbrev projLeft : 𝔸(ULift.{u} (Fin (d + e)); S) ⟶ 𝔸(ULift.{u} (Fin d); S) :=
  reindex (fun a ↦ ULift.up (Fin.castAdd e a.down)) S

/-- The last `e` coordinates `𝔸^{d+e}_S ⟶ 𝔸^e_S`. -/
noncomputable abbrev projRight : 𝔸(ULift.{u} (Fin (d + e)); S) ⟶ 𝔸(ULift.{u} (Fin e); S) :=
  reindex (fun b ↦ ULift.up (Fin.natAdd d b.down)) S

/-- `𝔸^{d+e}_S` is the fibre product `𝔸^d_S ×_S 𝔸^e_S`, through the first `d` and the last `e`
coordinates. -/
theorem isPullback_reindex_add :
    IsPullback (projLeft S d e) (projRight S d e) (𝔸(ULift.{u} (Fin d); S) ↘ S)
      (𝔸(ULift.{u} (Fin e); S) ↘ S) := by
  have w : projLeft S d e ≫ 𝔸(ULift.{u} (Fin d); S) ↘ S =
      projRight S d e ≫ 𝔸(ULift.{u} (Fin e); S) ↘ S := by
    rw [reindex_over, reindex_over]
  refine ⟨⟨w⟩, ⟨PullbackCone.IsLimit.mk w (fun s ↦ homOfVector (s.fst ≫ 𝔸(_; S) ↘ S)
    fun k ↦ Fin.addCases (fun a ↦ s.fst.appTop (coord S (ULift.up a)))
      (fun b ↦ s.snd.appTop (coord S (ULift.up b))) k.down) ?_ ?_ ?_⟩⟩
  · intro s
    refine hom_ext ?_ fun ⟨a⟩ ↦ ?_
    · rw [Category.assoc, reindex_over, homOfVector_over]
    · rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, reindex_appTop_coord,
        homOfVector_appTop_coord]
      simp
  · intro s
    refine hom_ext ?_ fun ⟨b⟩ ↦ ?_
    · rw [Category.assoc, reindex_over, homOfVector_over]
      exact s.condition
    · rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, reindex_appTop_coord,
        homOfVector_appTop_coord]
      simp
  · intro s m h₁ h₂
    refine hom_ext ?_ fun ⟨k⟩ ↦ ?_
    · rw [homOfVector_over, ← h₁, Category.assoc, reindex_over]
    · rw [homOfVector_appTop_coord]
      induction k using Fin.addCases with
      | left a =>
        rw [Fin.addCases_left, ← h₁, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
          reindex_appTop_coord]
      | right b =>
        rw [Fin.addCases_right, ← h₂, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
          reindex_appTop_coord]

end AffineSpace

namespace VectorBundle

variable {V S : Scheme.{u}} {d : ℕ} {π : V ⟶ S} (E : VectorBundle d π)

/-! ### Restricting a chart -/

section Restrict

variable (i : E.ι) (W : S.Opens) (h : W ≤ E.U i)

/-- The open `π⁻¹ W ⊆ π⁻¹(U i)` is the base change of `W ⊆ U i`. -/
lemma isPullback_homOfLE :
    IsPullback (V.homOfLE (π.preimage_mono h)) (π ∣_ W) (π ∣_ E.U i) (S.homOfLE h) := by
  have p : V.homOfLE (π.preimage_mono h) ≫ π ∣_ E.U i = π ∣_ W ≫ S.homOfLE h := by
    rw [← cancel_mono (E.U i).ι, Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι_assoc,
      Category.assoc, Scheme.homOfLE_ι, morphismRestrict_ι]
  refine IsPullback.of_right ?_ p (isPullback_morphismRestrict π (E.U i)).flip
  rw [Scheme.homOfLE_ι, Scheme.homOfLE_ι]
  exact (isPullback_morphismRestrict π W).flip

lemma isPullback_homOfLE_chart :
    IsPullback (V.homOfLE (π.preimage_mono h) ≫ (E.chart i).hom) (π ∣_ W)
      (𝔸(ULift.{u} (Fin d); E.U i) ↘ E.U i) (S.homOfLE h) := by
  have hc : IsPullback (E.chart i).hom (π ∣_ E.U i) (𝔸(ULift.{u} (Fin d); E.U i) ↘ E.U i)
      (𝟙 _) := IsPullback.of_horiz_isIso ⟨by rw [E.chart_over, Category.comp_id]⟩
  have hA := (E.isPullback_homOfLE i W h).paste_horiz hc
  rwa [Category.comp_id] at hA

/-- The chart of `π` over `U i` restricted to an open `W ⊆ U i`, `π⁻¹ W ≅ 𝔸^d_W`. -/
noncomputable def chartRestrict : (π ⁻¹ᵁ W).toScheme ≅ 𝔸(ULift.{u} (Fin d); W) :=
  (E.isPullback_homOfLE_chart i W h).isoIsPullback _ _
    (AffineSpace.isPullback_map (n := ULift.{u} (Fin d)) (S.homOfLE h))

@[reassoc (attr := simp)]
lemma chartRestrict_hom_over :
    (E.chartRestrict i W h).hom ≫ 𝔸(ULift.{u} (Fin d); W) ↘ W = π ∣_ W := by
  exact IsPullback.isoIsPullback_hom_snd _ _ _ _

@[reassoc (attr := simp)]
lemma chartRestrict_hom_map :
    (E.chartRestrict i W h).hom ≫ AffineSpace.map (ULift.{u} (Fin d)) (S.homOfLE h) =
      V.homOfLE (π.preimage_mono h) ≫ (E.chart i).hom :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- The coordinates of a restricted chart are the restrictions of the coordinates. -/
lemma chartRestrict_hom_appTop_coord (a : Fin d) :
    (E.chartRestrict i W h).hom.appTop (AffineSpace.coord _ (ULift.up a)) =
      (V.homOfLE (π.preimage_mono h)).appTop (E.coord i a) := by
  have key : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (k : Y ⟶ Z) (x : Γ(Z, ⊤)),
      (f ≫ k).appTop x = f.appTop (k.appTop x) := fun f k x ↦ by
    rw [Scheme.Hom.comp_appTop]
    rfl
  rw [coord, ← key, ← chartRestrict_hom_map, key, AffineSpace.map_appTop_coord]

end Restrict

/-! ### The direct sum -/

section Sum

variable {X : Scheme.{u}} {e : ℕ} {ρ : X ⟶ S} (F : VectorBundle e ρ)

/-- The structure morphism `V ×_S X ⟶ S` of the direct sum. -/
noncomputable abbrev sumπ : pullback π ρ ⟶ S := pullback.snd π ρ ≫ ρ

lemma sumπ_eq : sumπ (π := π) (ρ := ρ) = pullback.fst π ρ ≫ π := pullback.condition.symm

lemma preimage_sumπ_le_fst (A B : S.Opens) (h : A ≤ B) :
    sumπ (π := π) (ρ := ρ) ⁻¹ᵁ A ≤ pullback.fst π ρ ⁻¹ᵁ π ⁻¹ᵁ B := by
  rw [← Scheme.Hom.comp_preimage, ← sumπ_eq]
  exact Scheme.Hom.preimage_mono _ h

lemma preimage_sumπ_le_snd (A B : S.Opens) (h : A ≤ B) :
    sumπ (π := π) (ρ := ρ) ⁻¹ᵁ A ≤ pullback.snd π ρ ⁻¹ᵁ ρ ⁻¹ᵁ B := by
  rw [← Scheme.Hom.comp_preimage]
  exact Scheme.Hom.preimage_mono _ h

/-- The first projection of the direct sum over opens `A ≤ B`. -/
noncomputable def fstRes (A B : S.Opens) (h : A ≤ B) :
    (sumπ (π := π) (ρ := ρ) ⁻¹ᵁ A).toScheme ⟶ (π ⁻¹ᵁ B).toScheme :=
  (pullback.fst π ρ).resLE _ _ (preimage_sumπ_le_fst A B h)

/-- The second projection of the direct sum over opens `A ≤ B`. -/
noncomputable def sndRes (A B : S.Opens) (h : A ≤ B) :
    (sumπ (π := π) (ρ := ρ) ⁻¹ᵁ A).toScheme ⟶ (ρ ⁻¹ᵁ B).toScheme :=
  (pullback.snd π ρ).resLE _ _ (preimage_sumπ_le_snd A B h)

@[reassoc (attr := simp)]
lemma fstRes_ι (A B : S.Opens) (h : A ≤ B) :
    fstRes (π := π) (ρ := ρ) A B h ≫ (π ⁻¹ᵁ B).ι
      = (sumπ (π := π) (ρ := ρ) ⁻¹ᵁ A).ι ≫ pullback.fst π ρ :=
  Scheme.Hom.resLE_comp_ι _ _

@[reassoc (attr := simp)]
lemma sndRes_ι (A B : S.Opens) (h : A ≤ B) :
    sndRes (π := π) (ρ := ρ) A B h ≫ (ρ ⁻¹ᵁ B).ι
      = (sumπ (π := π) (ρ := ρ) ⁻¹ᵁ A).ι ≫ pullback.snd π ρ :=
  Scheme.Hom.resLE_comp_ι _ _

@[reassoc]
lemma homOfLE_fstRes (A A' B : S.Opens) (h : A ≤ B) (h' : A' ≤ A) :
    (pullback π ρ).homOfLE (Scheme.Hom.preimage_mono _ h') ≫ fstRes (π := π) (ρ := ρ) A B h =
      fstRes (π := π) (ρ := ρ) A' B (h'.trans h) := by
  rw [← cancel_mono (π ⁻¹ᵁ B).ι, Category.assoc, fstRes_ι, fstRes_ι, Scheme.homOfLE_ι_assoc]

@[reassoc]
lemma fstRes_homOfLE (A B B' : S.Opens) (h : A ≤ B) (h' : B ≤ B') :
    fstRes (π := π) (ρ := ρ) A B h ≫ V.homOfLE (π.preimage_mono h')
      = fstRes (π := π) (ρ := ρ) A B' (h.trans h') := by
  rw [← cancel_mono (π ⁻¹ᵁ B').ι, Category.assoc, Scheme.homOfLE_ι, fstRes_ι, fstRes_ι]

@[reassoc]
lemma homOfLE_sndRes (A A' B : S.Opens) (h : A ≤ B) (h' : A' ≤ A) :
    (pullback π ρ).homOfLE (Scheme.Hom.preimage_mono _ h') ≫ sndRes (π := π) (ρ := ρ) A B h =
      sndRes (π := π) (ρ := ρ) A' B (h'.trans h) := by
  rw [← cancel_mono (ρ ⁻¹ᵁ B).ι, Category.assoc, sndRes_ι, sndRes_ι, Scheme.homOfLE_ι_assoc]

@[reassoc]
lemma sndRes_homOfLE (A B B' : S.Opens) (h : A ≤ B) (h' : B ≤ B') :
    sndRes (π := π) (ρ := ρ) A B h ≫ X.homOfLE (ρ.preimage_mono h')
      = sndRes (π := π) (ρ := ρ) A B' (h.trans h') := by
  rw [← cancel_mono (ρ ⁻¹ᵁ B').ι, Category.assoc, Scheme.homOfLE_ι, sndRes_ι, sndRes_ι]

@[reassoc]
lemma fstRes_morphismRestrict (A B : S.Opens) (h : A ≤ B) :
    fstRes (π := π) (ρ := ρ) A B h ≫ π ∣_ B = sumπ (π := π) (ρ := ρ) ∣_ A ≫ S.homOfLE h := by
  rw [← cancel_mono B.ι, Category.assoc, morphismRestrict_ι, fstRes_ι_assoc, Category.assoc,
    Scheme.homOfLE_ι, morphismRestrict_ι, sumπ_eq]

@[reassoc]
lemma sndRes_morphismRestrict (A B : S.Opens) (h : A ≤ B) :
    sndRes (π := π) (ρ := ρ) A B h ≫ ρ ∣_ B = sumπ (π := π) (ρ := ρ) ∣_ A ≫ S.homOfLE h := by
  rw [← cancel_mono B.ι, Category.assoc, morphismRestrict_ι, sndRes_ι_assoc, Category.assoc,
    Scheme.homOfLE_ι, morphismRestrict_ι]

/-- The direct sum restricted to an open `W` of the base is the fibre product of the
restrictions. -/
lemma isPullback_fstRes_sndRes (W : S.Opens) :
    IsPullback (fstRes (π := π) (ρ := ρ) W W le_rfl) (sndRes (π := π) (ρ := ρ) W W le_rfl) (π ∣_ W) (ρ ∣_ W) := by
  have w : fstRes (π := π) (ρ := ρ) W W le_rfl ≫ π ∣_ W
      = sndRes (π := π) (ρ := ρ) W W le_rfl ≫ ρ ∣_ W := by
    rw [fstRes_morphismRestrict, sndRes_morphismRestrict]
  have hR : IsPullback (sumπ (π := π) (ρ := ρ) ⁻¹ᵁ W).ι (sndRes (π := π) (ρ := ρ) W W le_rfl)
      (pullback.snd π ρ) (ρ ⁻¹ᵁ W).ι := by
    have := (isPullback_morphismRestrict (pullback.snd π ρ) (ρ ⁻¹ᵁ W)).flip
    rw [← Scheme.Hom.resLE_eq_morphismRestrict] at this
    exact this
  have hB : IsPullback (pullback.fst π ρ) (pullback.snd π ρ) π ρ :=
    IsPullback.of_hasPullback π ρ
  have hout : IsPullback (fstRes (π := π) (ρ := ρ) W W le_rfl ≫ (π ⁻¹ᵁ W).ι) (sndRes (π := π) (ρ := ρ) W W le_rfl) π
      (ρ ∣_ W ≫ W.ι) := by
    rw [fstRes_ι, morphismRestrict_ι]
    exact hR.paste_horiz hB
  exact IsPullback.of_right hout w (isPullback_morphismRestrict π W).flip

/-- The trivialising open `U i ⊓ U' j` of the direct sum. -/
noncomputable abbrev sumU (p : E.ι × F.ι) : S.Opens := E.U p.1 ⊓ F.U p.2

lemma isPullback_sumChart (p : E.ι × F.ι) :
    IsPullback (fstRes (π := π) (ρ := ρ) (E.sumU F p) (E.sumU F p) le_rfl ≫
        (E.chartRestrict p.1 (E.sumU F p) inf_le_left).hom)
      (sndRes (π := π) (ρ := ρ) (E.sumU F p) (E.sumU F p) le_rfl ≫
        (F.chartRestrict p.2 (E.sumU F p) inf_le_right).hom)
      (𝔸(ULift.{u} (Fin d); E.sumU F p) ↘ E.sumU F p)
      (𝔸(ULift.{u} (Fin e); E.sumU F p) ↘ E.sumU F p) := by
  · have h₁ : IsPullback (E.chartRestrict p.1 (E.sumU F p) inf_le_left).hom
        (π ∣_ E.sumU F p) (𝔸(ULift.{u} (Fin d); E.sumU F p) ↘ E.sumU F p) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by rw [chartRestrict_hom_over, Category.comp_id]⟩
    have h₂ : IsPullback (ρ ∣_ E.sumU F p) (F.chartRestrict p.2 (E.sumU F p) inf_le_right).hom
        (𝟙 _) (𝔸(ULift.{u} (Fin e); E.sumU F p) ↘ E.sumU F p) :=
      IsPullback.of_vert_isIso ⟨by rw [chartRestrict_hom_over, Category.comp_id]⟩
    have h := ((isPullback_fstRes_sndRes (E.sumU F p)).paste_horiz h₁).paste_vert h₂
    simpa using h

/-- The chart of the direct sum over `U i ⊓ U' j`: the coordinates of the chart of `V` followed
by those of the chart of `X`. -/
noncomputable def sumChart (p : E.ι × F.ι) :
    (sumπ (π := π) (ρ := ρ) ⁻¹ᵁ E.sumU F p).toScheme ≅
      𝔸(ULift.{u} (Fin (d + e)); E.sumU F p) :=
  (E.isPullback_sumChart F p).isoIsPullback _ _ (AffineSpace.isPullback_reindex_add _ d e)
@[reassoc (attr := simp)]
lemma sumChart_hom_projLeft (p : E.ι × F.ι) :
    (E.sumChart F p).hom ≫ AffineSpace.projLeft _ d e =
      fstRes (π := π) (ρ := ρ) (E.sumU F p) (E.sumU F p) le_rfl ≫
        (E.chartRestrict p.1 (E.sumU F p) inf_le_left).hom :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

@[reassoc (attr := simp)]
lemma sumChart_hom_projRight (p : E.ι × F.ι) :
    (E.sumChart F p).hom ≫ AffineSpace.projRight _ d e =
      sndRes (π := π) (ρ := ρ) (E.sumU F p) (E.sumU F p) le_rfl ≫
        (F.chartRestrict p.2 (E.sumU F p) inf_le_right).hom :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

lemma appTop_comp {X₁ X₂ X₃ : Scheme.{u}} (f : X₁ ⟶ X₂) (k : X₂ ⟶ X₃) (x : Γ(X₃, ⊤)) :
    (f ≫ k).appTop x = f.appTop (k.appTop x) := by
  rw [Scheme.Hom.comp_appTop]
  rfl

/-- The first `d` coordinates of the chart of the direct sum are those of `V`. -/
lemma sumChart_hom_appTop_coord_castAdd (p : E.ι × F.ι) (a : Fin d) :
    (E.sumChart F p).hom.appTop (AffineSpace.coord _ (ULift.up (Fin.castAdd e a))) =
      (fstRes (π := π) (ρ := ρ) (E.sumU F p) (E.U p.1) inf_le_left).appTop (E.coord p.1 a) := by
  rw [← AffineSpace.reindex_appTop_coord
    (fun a : ULift.{u} (Fin d) ↦ ULift.up (Fin.castAdd e a.down)),
    ← appTop_comp, sumChart_hom_projLeft, appTop_comp, chartRestrict_hom_appTop_coord,
    ← appTop_comp, fstRes_homOfLE _ _ _ _ inf_le_left]

/-- The last `e` coordinates of the chart of the direct sum are those of `X`. -/
lemma sumChart_hom_appTop_coord_natAdd (p : E.ι × F.ι) (b : Fin e) :
    (E.sumChart F p).hom.appTop (AffineSpace.coord _ (ULift.up (Fin.natAdd d b))) =
      (sndRes (π := π) (ρ := ρ) (E.sumU F p) (F.U p.2) inf_le_right).appTop (F.coord p.2 b) := by
  rw [← AffineSpace.reindex_appTop_coord
    (fun b : ULift.{u} (Fin e) ↦ ULift.up (Fin.natAdd d b.down)),
    ← appTop_comp, sumChart_hom_projRight, appTop_comp, chartRestrict_hom_appTop_coord,
    ← appTop_comp, sndRes_homOfLE _ _ _ _ inf_le_right]

/-- The zero section of the direct sum. -/
noncomputable def sumZero : S ⟶ pullback π ρ :=
  pullback.lift E.zero F.zero (by rw [E.zero_comp, F.zero_comp])

@[reassoc (attr := simp)]
lemma sumZero_fst : E.sumZero F ≫ pullback.fst π ρ = E.zero := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma sumZero_snd : E.sumZero F ≫ pullback.snd π ρ = F.zero := pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
lemma sumZero_comp : E.sumZero F ≫ sumπ (π := π) (ρ := ρ) = 𝟙 S := by
  rw [sumZero_snd_assoc, F.zero_comp]

lemma sumZero_resLE_fstRes (p : E.ι × F.ι) :
    (E.sumZero F).resLE _ (E.sumU F p)
        (Scheme.Hom.le_preimage_preimage_of_comp_eq_id (E.sumZero_comp F) _) ≫
      fstRes (π := π) (ρ := ρ) (E.sumU F p) (E.U p.1) inf_le_left =
      S.homOfLE inf_le_left ≫ E.zeroRestrict p.1 := by
  rw [← cancel_mono (π ⁻¹ᵁ E.U p.1).ι, Category.assoc, fstRes_ι, Scheme.Hom.resLE_comp_ι_assoc,
    sumZero_fst, Category.assoc, zeroRestrict_ι, Scheme.homOfLE_ι_assoc]

lemma sumZero_resLE_sndRes (p : E.ι × F.ι) :
    (E.sumZero F).resLE _ (E.sumU F p)
        (Scheme.Hom.le_preimage_preimage_of_comp_eq_id (E.sumZero_comp F) _) ≫
      sndRes (π := π) (ρ := ρ) (E.sumU F p) (F.U p.2) inf_le_right =
      S.homOfLE inf_le_right ≫ F.zeroRestrict p.2 := by
  rw [← cancel_mono (ρ ⁻¹ᵁ F.U p.2).ι, Category.assoc, sndRes_ι, Scheme.Hom.resLE_comp_ι_assoc,
    sumZero_snd, Category.assoc, zeroRestrict_ι, Scheme.homOfLE_ι_assoc]

lemma sumChart_hom_over (p : E.ι × F.ι) :
    (E.sumChart F p).hom ≫ 𝔸(ULift.{u} (Fin (d + e)); E.sumU F p) ↘ E.sumU F p =
      sumπ (π := π) (ρ := ρ) ∣_ E.sumU F p := by
  rw [← AffineSpace.reindex_over (fun a : ULift.{u} (Fin d) ↦ ULift.up (Fin.castAdd e a.down)),
    sumChart_hom_projLeft_assoc, chartRestrict_hom_over,
    fstRes_morphismRestrict, Scheme.homOfLE_rfl, Category.comp_id]

/-- Blueprint `def-asd-vector-bundle-zero-section`: Vector bundles

**Direct sum.** For vector bundles `π : V ⟶ S` of rank `d` and `ρ : X ⟶ S` of rank `e`, the fibre
product `V ×_S X ⟶ S` is a vector bundle of rank `d + e`, trivialised over the intersections of
the trivialising opens, with the coordinates of `V` followed by those of `X`. -/
noncomputable def sum : VectorBundle (d + e) (sumπ (π := π) (ρ := ρ)) where
  zero := E.sumZero F
  zero_comp := E.sumZero_comp F
  ι := E.ι × F.ι
  U := E.sumU F
  iSup_U := by
    rw [← iSup_inf_iSup, E.iSup_U, F.iSup_U, top_inf_eq]
  chart := E.sumChart F
  chart_over := E.sumChart_hom_over F
  zero_chart p := by
    refine AffineSpace.hom_ext ?_ fun ⟨k⟩ ↦ ?_
    · rw [Category.assoc, sumChart_hom_over, AffineSpace.zeroSection_over,
        ← cancel_mono (E.sumU F p).ι, Category.assoc, morphismRestrict_ι,
        Scheme.Hom.resLE_comp_ι_assoc, sumZero_comp, Category.comp_id, Category.id_comp]
    · rw [appTop_comp, AffineSpace.zeroSection_appTop_coord]
      induction k using Fin.addCases with
      | left a =>
        rw [sumChart_hom_appTop_coord_castAdd, ← appTop_comp, sumZero_resLE_fstRes,
          appTop_comp, coord_zeroRestrict, map_zero]
      | right b =>
        rw [sumChart_hom_appTop_coord_natAdd, ← appTop_comp, sumZero_resLE_sndRes,
          appTop_comp, coord_zeroRestrict, map_zero]
  linear p q := by
    obtain ⟨ME, hME, hlinE⟩ := E.linear p.1 q.1
    obtain ⟨MF, hMF, hlinF⟩ := F.linear p.2 q.2
    have hOE : E.sumU F p ⊓ E.sumU F q ≤ E.U p.1 ⊓ E.U q.1 :=
      inf_le_inf inf_le_left inf_le_left
    have hOF : E.sumU F p ⊓ E.sumU F q ≤ F.U p.2 ⊓ F.U q.2 :=
      inf_le_inf inf_le_right inf_le_right
    let rE := (S.homOfLE hOE).appTop.hom
    let rF := (S.homOfLE hOF).appTop.hom
    let M : Matrix (Fin (d + e)) (Fin (d + e)) Γ((E.sumU F p ⊓ E.sumU F q).toScheme, ⊤) :=
      Matrix.of fun k l ↦ Fin.addCases (fun a ↦ Fin.addCases (fun b ↦ rE (ME a b)) (fun _ ↦ 0) l)
        (fun a ↦ Fin.addCases (fun _ ↦ 0) (fun b ↦ rF (MF a b)) l) k
    have hM : M = Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (ME.map rE) 0 0 (MF.map rF)) := by
      ext k l
      induction k using Fin.addCases <;> induction l using Fin.addCases <;> simp [M]
    refine ⟨M, ?_, fun k ↦ ?_⟩
    · have h₁ := hME.map rE
      have h₂ := hMF.map rF
      rw [RingHom.map_det] at h₁ h₂
      rw [hM, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]
      exact h₁.mul h₂
    have hfst : ∀ (k : E.ι) (A : S.Opens) (h : E.sumU F p ⊓ E.sumU F q ≤ E.U k) (h₀ : A ≤ E.U k)
        (h' : E.sumU F p ⊓ E.sumU F q ≤ A) (x : Γ((π ⁻¹ᵁ E.U k).toScheme, ⊤)),
        ((pullback π ρ).homOfLE (Scheme.Hom.preimage_mono _ h')).appTop
          ((fstRes (π := π) (ρ := ρ) _ _ h₀).appTop x) =
          (fstRes (π := π) (ρ := ρ) _ _ h).appTop x := fun k A h h₀ h' x ↦ by
      rw [← appTop_comp, homOfLE_fstRes _ _ _ h₀ h']
    have hfst' : ∀ (k : E.ι) (h : E.sumU F p ⊓ E.sumU F q ≤ E.U k)
        (h₀ : E.sumU F p ⊓ E.sumU F q ≤ E.U p.1 ⊓ E.U q.1)
        (h' : E.U p.1 ⊓ E.U q.1 ≤ E.U k) (x : Γ((π ⁻¹ᵁ E.U k).toScheme, ⊤)),
        (fstRes (π := π) (ρ := ρ) _ _ h₀).appTop ((V.homOfLE (π.preimage_mono h')).appTop x) =
          (fstRes (π := π) (ρ := ρ) _ _ h).appTop x := fun k h h₀ h' x ↦ by
      rw [← appTop_comp, fstRes_homOfLE _ _ _ h₀ h']
    have hsnd : ∀ (k : F.ι) (A : S.Opens) (h : E.sumU F p ⊓ E.sumU F q ≤ F.U k) (h₀ : A ≤ F.U k)
        (h' : E.sumU F p ⊓ E.sumU F q ≤ A) (x : Γ((ρ ⁻¹ᵁ F.U k).toScheme, ⊤)),
        ((pullback π ρ).homOfLE (Scheme.Hom.preimage_mono _ h')).appTop
          ((sndRes (π := π) (ρ := ρ) _ _ h₀).appTop x) =
          (sndRes (π := π) (ρ := ρ) _ _ h).appTop x := fun k A h h₀ h' x ↦ by
      rw [← appTop_comp, homOfLE_sndRes _ _ _ h₀ h']
    have hsnd' : ∀ (k : F.ι) (h : E.sumU F p ⊓ E.sumU F q ≤ F.U k)
        (h₀ : E.sumU F p ⊓ E.sumU F q ≤ F.U p.2 ⊓ F.U q.2)
        (h' : F.U p.2 ⊓ F.U q.2 ≤ F.U k) (x : Γ((ρ ⁻¹ᵁ F.U k).toScheme, ⊤)),
        (sndRes (π := π) (ρ := ρ) _ _ h₀).appTop ((X.homOfLE (ρ.preimage_mono h')).appTop x) =
          (sndRes (π := π) (ρ := ρ) _ _ h).appTop x := fun k h h₀ h' x ↦ by
      rw [← appTop_comp, sndRes_homOfLE _ _ _ h₀ h']
    have hrE : ∀ x, (fstRes (π := π) (ρ := ρ) _ _ hOE).appTop
        ((π ∣_ (E.U p.1 ⊓ E.U q.1)).appTop x) =
        (sumπ (π := π) (ρ := ρ) ∣_ (E.sumU F p ⊓ E.sumU F q)).appTop (rE x) := fun x ↦ by
      rw [← appTop_comp, fstRes_morphismRestrict, appTop_comp]
    have hrF : ∀ x, (sndRes (π := π) (ρ := ρ) _ _ hOF).appTop
        ((ρ ∣_ (F.U p.2 ⊓ F.U q.2)).appTop x) =
        (sumπ (π := π) (ρ := ρ) ∣_ (E.sumU F p ⊓ E.sumU F q)).appTop (rF x) := fun x ↦ by
      rw [← appTop_comp, sndRes_morphismRestrict, appTop_comp]
    change (_ ≫ (E.sumChart F q).hom).appTop _ = ∑ l, _ * (_ ≫ (E.sumChart F p).hom).appTop _
    simp only [appTop_comp]
    rw [Fin.sum_univ_add]
    induction k using Fin.addCases with
    | left a =>
      have hl := hlinE a
      simp only [appTop_comp] at hl
      rw [sumChart_hom_appTop_coord_castAdd,
        hfst _ _ (inf_le_right.trans inf_le_left) _ inf_le_right,
        ← hfst' _ _ hOE inf_le_right, coord, hl, map_sum]
      simp only [sumChart_hom_appTop_coord_castAdd, sumChart_hom_appTop_coord_natAdd,
        M,
        Matrix.of_apply, Fin.addCases_left, Fin.addCases_right, map_zero, zero_mul,
        Finset.sum_const_zero, add_zero, map_mul, hrE]
      refine Finset.sum_congr rfl fun b _ ↦ ?_
      rw [hfst' _ (inf_le_left.trans inf_le_left) hOE inf_le_left,
        hfst _ _ (inf_le_left.trans inf_le_left) _ inf_le_left]
      rfl
    | right a =>
      have hl := hlinF a
      simp only [appTop_comp] at hl
      rw [sumChart_hom_appTop_coord_natAdd,
        hsnd _ _ (inf_le_right.trans inf_le_right) _ inf_le_right,
        ← hsnd' _ _ hOF inf_le_right, coord, hl, map_sum]
      simp only [sumChart_hom_appTop_coord_castAdd, sumChart_hom_appTop_coord_natAdd,
        M,
        Matrix.of_apply, Fin.addCases_left, Fin.addCases_right, map_zero, zero_mul,
        Finset.sum_const_zero, zero_add, map_mul, hrF]
      refine Finset.sum_congr rfl fun b _ ↦ ?_
      rw [hsnd' _ (inf_le_left.trans inf_le_right) hOF inf_le_left,
        hsnd _ _ (inf_le_left.trans inf_le_right) _ inf_le_left]
      rfl

end Sum

end VectorBundle

end AlgebraicGeometry
