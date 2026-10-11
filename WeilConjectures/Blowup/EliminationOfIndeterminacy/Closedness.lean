/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Blowup.EliminationOfIndeterminacy.Coordinates
public import WeilConjectures.Blowup.EliminationOfIndeterminacy.GraphClosedness

/-!
# Closedness of the graph of the glued extension

The graph of the glued extension to relative affine space is closed: on the chart at a generator
`c` of the centre it is cut out by the equations `(d/c) · tⱼ = (bⱼ/c)`
(`AlgebraicGeometry.Scheme.IdealSheafData.isClosed_range_pullbackLift_of_awaySlope`).
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits HomogeneousLocalization

namespace AlgebraicGeometry
section Closedness

variable {A : Type u} [CommRing A] {I : Ideal A}
variable {X : Scheme.{u}}

set_option maxHeartbeats 600000 in
-- Unifying the `HomogeneousLocalization` chart rings exceeds the default heartbeat limit.
/-- **Closedness of the graph of the glued extension.** -/
lemma Scheme.IdealSheafData.isClosed_range_pullbackLift_of_awaySlope
    (K : X.IdealSheafData) (V : X.affineOpens) {σ ι : Type u}
    {a : ι → Γ(X, V.1)} (ha : ∀ i, a i ∈ K.ideal V)
    {b : ι → σ → Γ(X, V.1)} (hb : ∀ i j, b i j ∈ K.ideal V)
    (hrel : ∀ i i' j, b i j * a i' = b i' j * a i)
    (hspan : Ideal.span (Set.range (Sum.elim a fun p : ι × σ ↦ b p.1 p.2)) = K.ideal V)
    (hcover : ∀ z : K.blowup, z ∈ K.blowupMap ⁻¹ᵁ V.1)
    {W : K.blowup.Opens} (hW : W = ⨆ i, (K.blowupChart V (ha i)).opensRange)
    (ci : ∀ i : ι, Spec (.of (HomogeneousLocalization.Away (reesGrading (K.ideal V))
      (reesX (K.ideal V) (a i) (ha i)))) ⟶ W.toScheme)
    (hci : ∀ i, ci i ≫ W.ι = K.blowupChart V (ha i))
    (g : W.toScheme ⟶ 𝔸(σ; X)) (hg : g ≫ 𝔸(σ; X) ↘ X = W.ι ≫ K.blowupMap)
    (hgi : ∀ i, ci i ≫ g = AffineSpace.homOfVector (K.blowupChart V (ha i) ≫ K.blowupMap)
      (fun j ↦ (Scheme.ΓSpecIso _).inv
        (AffineBlowup.awaySlope (K.ideal V) (ha i) (hb i j)))) :
    IsClosed (Set.range (pullback.lift W.ι g hg.symm)) := by
  classical
  set gen : ι ⊕ ι × σ → Γ(X, V.1) := Sum.elim a fun p ↦ b p.1 p.2 with hgendef
  have hgen : ∀ k, gen k ∈ K.ideal V := by
    rintro (i | ⟨i, j⟩)
    · exact ha i
    · exact hb i j
  -- the base change of the `k`-th chart to the graph space
  have hlift : ∀ k, ((𝔸(σ; Spec (.of (HomogeneousLocalization.Away (reesGrading (K.ideal V))
        (reesX (K.ideal V) (gen k) (hgen k))))) ↘ _) ≫ K.blowupChart V (hgen k)) ≫
        K.blowupMap =
      AffineSpace.map σ (K.blowupChart V (hgen k) ≫ K.blowupMap) ≫ 𝔸(σ; X) ↘ X := by
    intro k
    rw [Category.assoc, AffineSpace.map_over]
  let qk : ∀ k, 𝔸(σ; Spec (.of (HomogeneousLocalization.Away (reesGrading (K.ideal V))
      (reesX (K.ideal V) (gen k) (hgen k))))) ⟶ pullback K.blowupMap (𝔸(σ; X) ↘ X) :=
    fun k ↦ pullback.lift _ _ (hlift k)
  have hqk_fst : ∀ k, qk k ≫ pullback.fst K.blowupMap (𝔸(σ; X) ↘ X) =
      (𝔸(σ; _) ↘ _) ≫ K.blowupChart V (hgen k) := fun k ↦ pullback.lift_fst _ _ _
  have hqk_snd : ∀ k, qk k ≫ pullback.snd K.blowupMap (𝔸(σ; X) ↘ X) =
      AffineSpace.map σ (K.blowupChart V (hgen k) ≫ K.blowupMap) :=
    fun k ↦ pullback.lift_snd _ _ _
  have hpb : ∀ k, IsPullback (qk k) (𝔸(σ; _) ↘ _)
      (pullback.fst K.blowupMap (𝔸(σ; X) ↘ X)) (K.blowupChart V (hgen k)) := by
    intro k
    refine IsPullback.of_right ?_ (hqk_fst k)
      (IsPullback.of_hasPullback K.blowupMap (𝔸(σ; X) ↘ X)).flip
    rw [hqk_snd k]
    exact AffineSpace.isPullback_map (K.blowupChart V (hgen k) ≫ K.blowupMap)
  have : ∀ k, IsOpenImmersion (qk k) := fun k ↦ (hpb k).isOpenImmersion_fst
  refine Scheme.isClosed_of_openCover qk ?_ ?_
  · intro x
    have hx : pullback.fst K.blowupMap (𝔸(σ; X) ↘ X) x ∈ K.blowupMap ⁻¹ᵁ V.1 :=
      hcover _
    obtain ⟨k, y, hy⟩ := K.exists_mem_range_blowupChart_of_span V hgen hspan hx
    have hmem : x ∈ (qk k).opensRange := by
      rw [(hpb k).opensRange_fst]
      exact ⟨y, hy.symm⟩
    exact ⟨k, hmem.choose, hmem.choose_spec⟩
  · intro k
    have hsubO : Set.range ((K.blowupChart V (hgen k) ⁻¹ᵁ W).ι ≫
        K.blowupChart V (hgen k)).base ⊆ Set.range W.ι.base := by
      rintro - ⟨z, rfl⟩
      exact ⟨⟨_, z.2⟩, rfl⟩
    obtain ⟨lam, hlam⟩ : ∃ lam : (K.blowupChart V (hgen k) ⁻¹ᵁ W).toScheme ⟶ W.toScheme,
        lam ≫ W.ι = (K.blowupChart V (hgen k) ⁻¹ᵁ W).ι ≫ K.blowupChart V (hgen k) :=
      ⟨IsOpenImmersion.lift W.ι _ hsubO, IsOpenImmersion.lift_fac _ _ _⟩
    refine Scheme.isClosed_preimage_range_pullbackLift K.blowupMap g hg
      (K.blowupChart V (hgen k)) (qk k) (hqk_fst k) (hqk_snd k) lam hlam ?_
    -- the chart overlaps
    have hpre : ∀ i, K.blowupChart V (hgen k) ⁻¹ᵁ (K.blowupChart V (ha i)).opensRange =
        PrimeSpectrum.basicOpen (AffineBlowup.awaySlope (K.ideal V) (hgen k) (ha i)) :=
      fun i ↦ K.blowupChart_preimage_opensRange V (hgen k) (ha i)
    have hO : K.blowupChart V (hgen k) ⁻¹ᵁ W =
        ⨆ i, PrimeSpectrum.basicOpen (AffineBlowup.awaySlope (K.ideal V) (hgen k) (ha i)) := by
      refine TopologicalSpace.Opens.ext (Set.ext fun y ↦ ?_)
      constructor
      · intro hy
        have hy' : K.blowupChart V (hgen k) y ∈
            ⨆ i, (K.blowupChart V (ha i)).opensRange := hW ▸ hy
        obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hy'
        refine TopologicalSpace.Opens.mem_iSup.mpr ⟨i, ?_⟩
        rw [← hpre i]
        exact hi
      · intro hy
        obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
        rw [← hpre i] at hi
        have hi' : K.blowupChart V (hgen k) y ∈ (K.blowupChart V (ha i)).opensRange := hi
        exact hW ▸ TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi'⟩
    have hBle : ∀ i, PrimeSpectrum.basicOpen
        (AffineBlowup.awaySlope (K.ideal V) (hgen k) (ha i)) ≤
        K.blowupChart V (hgen k) ⁻¹ᵁ W := by
      intro i
      exact (le_iSup (fun i ↦ PrimeSpectrum.basicOpen
        (AffineBlowup.awaySlope (K.ideal V) (hgen k) (ha i))) i).trans_eq hO.symm
    -- `O` and `B` are passed explicitly: inferring them by unification is slow.
    refine AffineSpace.isClosed_range_of_basicOpen_fractions (O := K.blowupChart V (hgen k) ⁻¹ᵁ W)
      (B := fun i ↦ PrimeSpectrum.basicOpen (AffineBlowup.awaySlope (K.ideal V) (hgen k) (ha i)))
      (fun i ↦ AffineBlowup.awaySlope (K.ideal V) (hgen k) (ha i))
      (fun i j ↦ AffineBlowup.awaySlope (K.ideal V) (hgen k) (hb i j)) ?_ ?_
      (fun i ↦ rfl) hO _ (AffineSpace.homOfVector_over _ _) hBle ?_
    · -- the slopes of the generators generate the unit ideal
      refine Ideal.span_mono ?_
        (AffineBlowup.one_mem_span_awaySlope gen hgen hspan (hgen k))
      rintro - ⟨(i | ⟨i, j⟩), rfl⟩
      · exact Or.inl ⟨i, rfl⟩
      · exact Or.inr (Set.mem_iUnion.mpr ⟨i, j, rfl⟩)
    · -- the compatibility of the fractions
      intro i i' j
      refine AffineBlowup.awaySlope_mul_awaySlope (hgen k) (ha i) (hb i' j) (ha i')
        (hb i j) ?_
      rw [mul_comm (a i), hrel i' i j, mul_comm]
    · -- the coordinate identity on each piece
      intro i j
      -- The goal and the type of the lemma agree up to unfolding, but not syntactically.
      -- `convert` matches them argument by argument and closes every resulting goal by `rfl`;
      -- `exact` checks the definitional equality at once, unfolding the chart rings, and makes
      -- the file about four times slower.
      convert K.mul_appTop_coord_awaySlope V g (hgen k) lam hlam (ha i) (hb i) (ci i) (hci i)
        (hgi i) rfl (hBle i) j using 2

end Closedness

end AlgebraicGeometry
