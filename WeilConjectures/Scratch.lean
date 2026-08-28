module

public import WeilConjectures.Blowup.EliminationOfIndeterminacy

@[expose] public section

noncomputable section
universe u
open CategoryTheory Limits HomogeneousLocalization
namespace AlgebraicGeometry
open AffineSpace


/-- Two morphisms to a relative affine space with the same structure morphism agree if their
coordinates agree after multiplication by a unit. -/
lemma AffineSpace.hom_ext_of_mul_unit {S T : Scheme.{u}} {σ : Type u} {F G : T ⟶ 𝔸(σ; S)}
    (h₁ : F ≫ 𝔸(σ; S) ↘ S = G ≫ 𝔸(σ; S) ↘ S) {w : Γ(T, ⊤)} (hw : IsUnit w)
    (h₂ : ∀ j, w * F.appTop (AffineSpace.coord S j) = w * G.appTop (AffineSpace.coord S j)) :
    F = G :=
  AffineSpace.hom_ext h₁ fun j ↦ hw.mul_left_cancel (h₂ j)

variable {X : Scheme.{u}}

/-- The `appLE` of a morphism between the top opens is its `appTop`. -/
lemma Scheme.Hom.appLE_top_top {T T' : Scheme.{u}} (q : T ⟶ T')
    (h : (⊤ : T.Opens) ≤ q ⁻¹ᵁ ⊤) : q.appLE ⊤ ⊤ h = q.appTop := by
  simp [Scheme.Hom.appLE]

set_option maxHeartbeats 4000000 in
-- Unifying the `HomogeneousLocalization` chart rings exceeds the default heartbeat limit.
/-- The global sections of the blow-up chart over an affine scheme pull sections of `X` back
through the structure map of the chart ring. -/
lemma Scheme.IdealSheafData.appTop_blowupChart_comp_blowupMap {X : Scheme.{u}} [IsAffine X]
    (K : X.IdealSheafData) {d : Γ(X, ⊤)} (hd : d ∈ K.ideal ⟨⊤, isAffineOpen_top X⟩)
    (r : Γ(X, ⊤)) :
    (K.blowupChart ⟨⊤, isAffineOpen_top X⟩ hd ≫ K.blowupMap).appTop r =
      (Scheme.ΓSpecIso _).inv (AffineBlowup.awayAlgebraMap
        (K.ideal ⟨⊤, isAffineOpen_top X⟩)
        (reesX (K.ideal ⟨⊤, isAffineOpen_top X⟩) d hd) r) := by
  rw [← Scheme.Hom.appLE_top_top _
      (K.blowupChart_comp_blowupMap_preimage ⟨⊤, isAffineOpen_top X⟩ hd),
    K.appLE_blowupChart_comp_blowupMap ⟨⊤, isAffineOpen_top X⟩ hd]
  rfl

/-- **The glued extension agrees with the partial map over a basic open of the centre.**
On the preimage of `D(d)` the blow-up is covered by a single chart `Spec R`, on which the
extension has coordinates `s j` with `φ d · s j = φ (b j)`; since `d` is invertible there,
this forces the extension to agree with any partial map whose coordinates satisfy
`coordⱼ · d = b j` on `D(d)`. -/
lemma Scheme.IdealSheafData.homOfLE_comp_eq_of_chart {X : Scheme.{u}} {σ : Type u}
    (K : X.IdealSheafData) {U : X.Opens} {W : K.blowup.Opens}
    (hWmem : K.blowupMap ⁻¹ᵁ U ≤ W) {f : U.toScheme ⟶ 𝔸(σ; X)}
    (hf : f ≫ 𝔸(σ; X) ↘ X = U.ι) (g : W.toScheme ⟶ 𝔸(σ; X))
    {R : CommRingCat.{u}} (chart : Spec R ⟶ K.blowup) [IsOpenImmersion chart]
    (φ : Γ(X, ⊤) ⟶ R)
    (hφ : ∀ r, (chart ≫ K.blowupMap).appTop r = (Scheme.ΓSpecIso R).inv (φ r))
    {d : Γ(X, ⊤)} {b : σ → Γ(X, ⊤)} (s : σ → R) (hs : ∀ j, φ d * s j = φ (b j))
    {D : X.Opens} (hD : X.basicOpen d = D) (hDU : D ≤ U)
    (hcoord : ∀ j, (X.homOfLE hDU ≫ f).appTop (AffineSpace.coord X j) * D.ι.appTop d =
      D.ι.appTop (b j))
    (ci : Spec R ⟶ W.toScheme) (hci : ci ≫ W.ι = chart)
    (hgi : ci ≫ g = AffineSpace.homOfVector (chart ≫ K.blowupMap)
      (fun j ↦ (Scheme.ΓSpecIso R).inv (s j)))
    (hDchart : K.blowupMap ⁻¹ᵁ D ≤ chart.opensRange) :
    K.blowup.homOfLE (K.blowupMap.preimage_mono hDU) ≫ K.blowup.homOfLE hWmem ≫ g =
      K.blowup.homOfLE (K.blowupMap.preimage_mono hDU) ≫ (K.blowupMap ∣_ U) ≫ f := by
  subst hD
  have hrange : Set.range (K.blowupMap ⁻¹ᵁ X.basicOpen d).ι.base ⊆
      Set.range chart.base := by
    intro z hz
    obtain ⟨z, rfl⟩ := hz
    exact hDchart z.2
  obtain ⟨θ, hθ⟩ : ∃ θ : (K.blowupMap ⁻¹ᵁ X.basicOpen d).toScheme ⟶ Spec R,
      θ ≫ chart = (K.blowupMap ⁻¹ᵁ X.basicOpen d).ι :=
    ⟨IsOpenImmersion.lift chart _ hrange, IsOpenImmersion.lift_fac _ _ _⟩
  have hleft : K.blowup.homOfLE (K.blowupMap.preimage_mono hDU) ≫
      K.blowup.homOfLE hWmem = θ ≫ ci := by
    rw [← cancel_mono W.ι, Category.assoc, Category.assoc, hci, Scheme.homOfLE_ι, hθ,
      Scheme.homOfLE_ι]
  rw [← Category.assoc, hleft, Category.assoc, hgi]
  have hres : K.blowup.homOfLE (K.blowupMap.preimage_mono hDU) ≫ (K.blowupMap ∣_ U) =
      (K.blowupMap ∣_ X.basicOpen d) ≫ X.homOfLE hDU := by
    rw [morphismRestrict_homOfLE]
  have hPι : (K.blowupMap ∣_ X.basicOpen d) ≫ (X.basicOpen d).ι =
      (K.blowupMap ⁻¹ᵁ X.basicOpen d).ι ≫ K.blowupMap := morphismRestrict_ι _ _
  have hunit : IsUnit (((K.blowupMap ⁻¹ᵁ X.basicOpen d).ι ≫ K.blowupMap).appTop d) := by
    refine Scheme.isUnit_of_le_basicOpen (le_of_eq ?_)
    rw [← Scheme.preimage_basicOpen_top]
    exact (Scheme.Opens.ι_preimage_self (K.blowupMap ⁻¹ᵁ X.basicOpen d)).symm
  have hθw : ∀ r : Γ(X, ⊤), ((K.blowupMap ⁻¹ᵁ X.basicOpen d).ι ≫ K.blowupMap).appTop r =
      θ.appTop ((chart ≫ K.blowupMap).appTop r) := by
    intro r
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, ← Category.assoc, hθ]
  have hρw : ∀ r : Γ(X, ⊤), ((K.blowupMap ⁻¹ᵁ X.basicOpen d).ι ≫ K.blowupMap).appTop r =
      (K.blowupMap ∣_ X.basicOpen d).appTop ((X.basicOpen d).ι.appTop r) := by
    intro r
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hPι]
  refine AffineSpace.hom_ext_of_mul_unit ?_ hunit fun j ↦ ?_
  · simp only [Category.assoc, AffineSpace.homOfVector_over, hf, morphismRestrict_ι]
    rw [← Category.assoc, hθ, ← Category.assoc, Scheme.homOfLE_ι]
  · have hL : ((K.blowupMap ⁻¹ᵁ X.basicOpen d).ι ≫ K.blowupMap).appTop d *
        (θ ≫ AffineSpace.homOfVector (chart ≫ K.blowupMap)
          (fun j ↦ (Scheme.ΓSpecIso R).inv (s j))).appTop (AffineSpace.coord X j) =
        ((K.blowupMap ⁻¹ᵁ X.basicOpen d).ι ≫ K.blowupMap).appTop (b j) := by
      rw [AffineSpace.comp_homOfVector_appTop_coord, hθw d, hθw (b j), hφ d, hφ (b j),
        ← map_mul, ← map_mul, hs j]
    have hR : ((K.blowupMap ⁻¹ᵁ X.basicOpen d).ι ≫ K.blowupMap).appTop d *
        (K.blowup.homOfLE (K.blowupMap.preimage_mono hDU) ≫
          (K.blowupMap ∣_ U) ≫ f).appTop (AffineSpace.coord X j) =
        ((K.blowupMap ⁻¹ᵁ X.basicOpen d).ι ≫ K.blowupMap).appTop (b j) := by
      have hmul : (X.basicOpen d).ι.appTop d *
          (X.homOfLE hDU ≫ f).appTop (AffineSpace.coord X j) =
          (X.basicOpen d).ι.appTop (b j) := by
        rw [mul_comm]
        exact hcoord j
      rw [← Category.assoc, hres, Category.assoc, hρw d, hρw (b j),
        Scheme.Hom.comp_appTop, CommRingCat.comp_apply, ← map_mul, hmul]
    exact hL.trans hR.symm

set_option maxHeartbeats 3200000 in
-- Unifying the `HomogeneousLocalization` chart rings exceeds the default heartbeat limit.
theorem test_extend [IsAffine X]
    {U : X.Opens} (hU : IsCompact (U : Set X)) {σ : Type u} [Finite σ]
    (f : U.toScheme ⟶ 𝔸(σ; X)) (hf : f ≫ 𝔸(σ; X) ↘ X = U.ι) :
    ∃ (B : IsAdmissible X U) (W : B.I.blowup.Opens) (hW : B.I.blowupMap ⁻¹ᵁ U ≤ W)
      (g : W.toScheme ⟶ 𝔸(σ; X)) (hg : g ≫ 𝔸(σ; X) ↘ X = W.ι ≫ B.I.blowupMap),
      B.I.blowup.homOfLE hW ≫ g = (B.I.blowupMap ∣_ U) ≫ f ∧
      IsClosed (Set.range (pullback.lift W.ι g hg.symm)) := by
  classical
  obtain ⟨ι, hιfin, u, hle, N, c, hUeq, hNpos, hrel, hcoord⟩ :=
    exists_uniform_denominator hU f
  -- the centre
  set gen : ι ⊕ ι × σ → Γ(X, ⊤) := Sum.elim (fun i ↦ u i ^ N) (fun p ↦ c p.1 p.2) with hgendef
  set I₀ : Ideal Γ(X, ⊤) := Ideal.span (Set.range gen) with hI₀def
  set V₀ : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩ with hV₀def
  set K : X.IdealSheafData := Scheme.IdealSheafData.ofIdealTop I₀ with hKdef
  have hKV₀ : K.ideal V₀ = I₀ := by
    rw [hKdef, Scheme.IdealSheafData.ofIdealTop_ideal]
    have h1 : (homOfLE (le_top (a := V₀.1))).op = 𝟙 _ := rfl
    rw [h1, CategoryTheory.Functor.map_id, CommRingCat.hom_id, Ideal.map_id]
  have hgen : ∀ k, gen k ∈ K.ideal V₀ := fun k ↦ hKV₀ ▸ Ideal.subset_span ⟨k, rfl⟩
  have hspan : Ideal.span (Set.range gen) = K.ideal V₀ := hKV₀.symm
  haveI : Finite (ι ⊕ ι × σ) := by
    haveI := hιfin
    infer_instance
  have hFG : I₀.FG := by
    haveI := hιfin
    haveI : Fintype (ι ⊕ ι × σ) := Fintype.ofFinite _
    exact ⟨Finset.image gen Finset.univ, by rw [hI₀def]; congr 1; simp [Set.image_univ]⟩
  have hFT : K.ofFiniteType := by
    intro V _
    rw [hKdef, Scheme.IdealSheafData.ofIdealTop_ideal]
    exact hFG.map _
  have hdisj : Disjoint (U : Set X) (K.support : Set X) := by
    rw [Set.disjoint_left]
    intro x hxU hxs
    rw [hKdef, Scheme.IdealSheafData.coe_support_ofIdealTop, Scheme.mem_zeroLocus_iff] at hxs
    rw [hUeq] at hxU
    obtain ⟨i, hxi⟩ := TopologicalSpace.Opens.mem_iSup.mp hxU
    exact hxs (u i ^ N) (Ideal.subset_span ⟨Sum.inl i, rfl⟩)
      (by rwa [Scheme.basicOpen_pow _ _ hNpos])
  have happLE : ∀ {T T' : Scheme.{u}} (q : T ⟶ T') (h : (⊤ : T.Opens) ≤ q ⁻¹ᵁ ⊤),
      q.appLE ⊤ ⊤ h = q.appTop := by
    intro T T' q h
    simp [Scheme.Hom.appLE]
  have happ : ∀ (k : ι ⊕ ι × σ) (r : Γ(X, ⊤)),
      (K.blowupChart V₀ (hgen k) ≫ K.blowupMap).appTop r =
        (Scheme.ΓSpecIso _).inv (AffineBlowup.awayAlgebraMap (K.ideal V₀)
          (reesX (K.ideal V₀) (gen k) (hgen k)) r) := by
    intro k r
    rw [← happLE _ (K.blowupChart_comp_blowupMap_preimage V₀ (hgen k)),
      K.appLE_blowupChart_comp_blowupMap V₀ (hgen k)]
    rfl
  -- the charts at the `u i ^ N` cover the preimage of `U`
  have hPchart : ∀ i : ι, K.blowupMap ⁻¹ᵁ X.basicOpen (u i) ≤
      (K.blowupChart V₀ (hgen (Sum.inl i))).opensRange := by
    intro i x hx
    have hxtop : x ∈ K.blowupMap ⁻¹ᵁ V₀.1 := trivial
    obtain ⟨k, y, rfl⟩ := K.exists_mem_range_blowupChart_of_span V₀ hgen hspan hxtop
    have hxi : K.blowupMap (K.blowupChart V₀ (hgen k) y) ∈ X.basicOpen (u i) := hx
    rw [← Scheme.Hom.comp_apply, K.blowupChart_comp_blowupMap V₀ (hgen k),
      Scheme.Hom.comp_apply] at hxi
    have hy : y ∈ PrimeSpectrum.basicOpen (AffineBlowup.awayAlgebraMap (K.ideal V₀)
        (reesX (K.ideal V₀) (gen k) (hgen k)) (u i)) := by
      have h1 : Spec.map (CommRingCat.ofHom (AffineBlowup.awayAlgebraMap (K.ideal V₀)
          (reesX (K.ideal V₀) (gen k) (hgen k)))) y ∈
          V₀.2.fromSpec ⁻¹ᵁ X.basicOpen (u i) := hxi
      rw [V₀.2.fromSpec_preimage_basicOpen] at h1
      exact h1
    have hyN : y ∈ PrimeSpectrum.basicOpen (AffineBlowup.awayAlgebraMap (K.ideal V₀)
        (reesX (K.ideal V₀) (gen k) (hgen k)) (u i ^ N)) := by
      rw [map_pow, PrimeSpectrum.basicOpen_pow _ _ hNpos]
      exact hy
    obtain ⟨z, hz⟩ := AffineBlowup.mem_range_chart_of_mem_basicOpen (hgen k)
      (hgen (Sum.inl i)) y hyN
    refine ⟨z, ?_⟩
    rw [Scheme.IdealSheafData.blowupChart, Scheme.IdealSheafData.blowupChart,
      Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hz]
  -- the open `W`
  set W : K.blowup.Opens := ⨆ i : ι, (K.blowupChart V₀ (hgen (Sum.inl i))).opensRange with hWdef
  have hWmem : K.blowupMap ⁻¹ᵁ U ≤ W := by
    intro x hx
    have hxU : K.blowupMap x ∈ ⨆ i : ι, X.basicOpen (u i) := by rw [← hUeq]; exact hx
    obtain ⟨i, hxi⟩ := TopologicalSpace.Opens.mem_iSup.mp hxU
    rw [hWdef]
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hPchart i hxi⟩
  -- the chart cover of `W` and the glued extension
  have hsub : ∀ i : ι, Set.range (K.blowupChart V₀ (hgen (Sum.inl i))).base ⊆
      Set.range W.ι.base := by
    intro i z hz
    have h1 : (K.blowupChart V₀ (hgen (Sum.inl i))).opensRange ≤ W := by
      rw [hWdef]
      exact le_iSup (fun i : ι ↦ (K.blowupChart V₀ (hgen (Sum.inl i))).opensRange) i
    exact ⟨⟨z, h1 hz⟩, rfl⟩
  set ci : ∀ i : ι, Spec (.of (HomogeneousLocalization.Away (reesGrading (K.ideal V₀))
      (reesX (K.ideal V₀) (gen (Sum.inl i)) (hgen (Sum.inl i))))) ⟶ W.toScheme :=
    fun i ↦ IsOpenImmersion.lift W.ι (K.blowupChart V₀ (hgen (Sum.inl i))) (hsub i) with hcidef
  have hci : ∀ i, ci i ≫ W.ι = K.blowupChart V₀ (hgen (Sum.inl i)) :=
    fun i ↦ IsOpenImmersion.lift_fac _ _ _
  obtain ⟨g, hg, hgi⟩ := K.exists_hom_affineSpace_of_awaySlope V₀
    (a := fun i ↦ gen (Sum.inl i)) (ha := fun i ↦ hgen (Sum.inl i))
    (b := fun i j ↦ gen (Sum.inr (i, j))) (hb := fun i j ↦ hgen (Sum.inr (i, j)))
    (fun i i' j ↦ hrel i i' j) W hWdef ci hci
  refine ⟨⟨K, hFT, hdisj⟩, W, hWmem, g, hg, ?_, ?_⟩
  · -- agreement over `U`
    have hPle : ∀ i : ι, K.blowupMap ⁻¹ᵁ X.basicOpen (u i) ≤ K.blowupMap ⁻¹ᵁ U :=
      fun i ↦ K.blowupMap.preimage_mono (hle i)
    have hcov2 : ∀ x : (K.blowupMap ⁻¹ᵁ U).toScheme,
        ∃ i y, (K.blowup.homOfLE (hPle i)) y = x := by
      intro x
      have hxU : K.blowupMap x.1 ∈ ⨆ i : ι, X.basicOpen (u i) := by
        rw [← hUeq]; exact x.2
      obtain ⟨i, hxi⟩ := TopologicalSpace.Opens.mem_iSup.mp hxU
      refine ⟨i, ⟨x.1, hxi⟩, (K.blowupMap ⁻¹ᵁ U).ι.isOpenEmbedding.injective ?_⟩
      rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]
      rfl
    refine Scheme.Cover.hom_ext (Scheme.Cover.mkOfCovers ι _
      (fun i ↦ K.blowup.homOfLE (hPle i)) hcov2) _ _ fun i ↦ ?_
    have hfi : (Scheme.Cover.mkOfCovers ι _
      (fun i ↦ K.blowup.homOfLE (hPle i)) hcov2).f i = K.blowup.homOfLE (hPle i) := rfl
    rw [hfi]
    exact K.homOfLE_comp_eq_of_chart hWmem hf g (K.blowupChart V₀ (hgen (Sum.inl i)))
      (CommRingCat.ofHom (AffineBlowup.awayAlgebraMap (K.ideal V₀)
        (reesX (K.ideal V₀) (gen (Sum.inl i)) (hgen (Sum.inl i)))))
      (K.appTop_blowupChart_comp_blowupMap (hgen (Sum.inl i)))
      (fun j ↦ AffineBlowup.awaySlope (K.ideal V₀) (hgen (Sum.inl i))
        (hgen (Sum.inr (i, j))))
      (fun j ↦ by
        rw [mul_comm]
        exact AffineBlowup.awaySlope_mul_awayAlgebraMap (hgen (Sum.inl i))
          (hgen (Sum.inr (i, j))))
      (Scheme.basicOpen_pow (X := X) (f := u i) hNpos) (hle i)
      (hcoord i) (ci i) (hci i) (hgi i) (hPchart i)
  · sorry

end AlgebraicGeometry
