module

public import WeilConjectures.Blowup.QuasiAffineGeneral
public import WeilConjectures.Blowup.GraphQuasiFinite
public import WeilConjectures.Blowup.PartialSectionExtensionReduction

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

theorem exists_admissibleBlowup_extend_partialSection'
    [CompactSpace X] [QuasiSeparatedSpace X] {U V : X.Opens} (hUV : U ≤ V)
    (hU : IsCompact (U : Set X)) (hV : IsCompact (V : Set X))
    (hUdense : Dense (U : Set X))
    {Y : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y] {p : Y ⟶ X}
    [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p]
    (f : U.toScheme ⟶ Y) (hf : f ≫ p = U.ι)
    (hfc : IsClosed ((p ⁻¹ᵁ V).ι ⁻¹' Set.range f)) :
    ∃ (B : IsAdmissible X V) (W : B.I.blowup.Opens) (hUW : B.I.blowupMap ⁻¹ᵁ U ≤ W)
      (g : W.toScheme ⟶ Y) (hg : g ≫ p = W.ι ≫ B.I.blowupMap),
      B.I.blowup.homOfLE hUW ≫ g = (B.I.blowupMap ∣_ U) ≫ f ∧
        IsClosed (Set.range (pullback.lift g W.ι hg)) := by
  -- **Step 2**: a `V`-admissible blow-up over which the graph has quasi-finite image.
  obtain ⟨B₁, σ, hσopen, hσ, hQF⟩ :=
    exists_isAdmissible_locallyQuasiFinite_image_graph hUV hU hV f hf hfc
  obtain ⟨F, hFfst, hFsnd⟩ :
      ∃ F : U.toScheme ⟶ pullback p B₁.I.blowupMap,
        F ≫ pullback.fst p B₁.I.blowupMap = f ∧
          F ≫ pullback.snd p B₁.I.blowupMap = σ :=
    ⟨pullback.lift f σ (by rw [hf, hσ]), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨hqf, hft, hsep, hqc⟩ := hQF F hFfst hFsnd
  haveI := hqf
  haveI := hft
  haveI := hsep
  haveI := hqc
  -- the section `σ` is the canonical isomorphism onto the preimage of `U`
  have hrange : Set.range σ ⊆ Set.range (B₁.I.blowupMap ⁻¹ᵁ U).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨u, rfl⟩
    change B₁.I.blowupMap (σ u) ∈ U
    rw [← Scheme.Hom.comp_apply, hσ]
    exact u.2
  set s : U.toScheme ⟶ (B₁.I.blowupMap ⁻¹ᵁ U).toScheme :=
    IsOpenImmersion.lift (B₁.I.blowupMap ⁻¹ᵁ U).ι σ hrange with hsdef
  have hsι : s ≫ (B₁.I.blowupMap ⁻¹ᵁ U).ι = σ := IsOpenImmersion.lift_fac _ _ _
  haveI : IsIso (B₁.I.blowupMap ∣_ U) :=
    IsAdmissible.isIso_blowupMap_restrict
      ⟨B₁.I, B₁.finiteType, B₁.disjoint_support.mono_left (show (U : Set X) ≤ V from hUV)⟩
  have hsid : s ≫ (B₁.I.blowupMap ∣_ U) = 𝟙 U.toScheme := by
    rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hsι, hσ,
      Category.id_comp]
  haveI : IsIso s := by
    have hs : s = inv (B₁.I.blowupMap ∣_ U) := by
      rw [← Category.comp_id s, ← IsIso.hom_inv_id (B₁.I.blowupMap ∣_ U), ← Category.assoc,
        hsid, Category.id_comp]
    rw [hs]
    infer_instance
  -- **The interface seam**: the two orientations of the fibre product `Y ×[X] X̃`.
  have hτfst : (pullbackSymmetry p B₁.I.blowupMap).hom ≫ pullback.fst B₁.I.blowupMap p
      = pullback.snd p B₁.I.blowupMap := pullbackSymmetry_hom_comp_fst
  have hτsnd : (pullbackSymmetry p B₁.I.blowupMap).hom ≫ pullback.snd B₁.I.blowupMap p
      = pullback.fst p B₁.I.blowupMap := pullbackSymmetry_hom_comp_snd
  have hbcs : s ≫ baseChangeSection f hf B₁
      = F ≫ (pullbackSymmetry p B₁.I.blowupMap).hom := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, baseChangeSection_comp_fst, hsι, Category.assoc, hτfst, hFsnd]
    · rw [Category.assoc, baseChangeSection_comp_snd, ← Category.assoc, hsid, Category.id_comp,
        Category.assoc, hτsnd, hFfst]
  -- **Step 3**: Zariski's Main Theorem makes the image quasi-affine over the blow-up.
  haveI : IsQuasiAffineHom (F.imageι ≫ pullback.snd p B₁.I.blowupMap) :=
    IsQuasiAffineHom.of_locallyQuasiFinite _
  set i : F.image ⟶ pullback B₁.I.blowupMap p :=
    F.imageι ≫ (pullbackSymmetry p B₁.I.blowupMap).hom with hidef
  haveI : IsClosedImmersion i := by rw [hidef]; infer_instance
  have hi : i ≫ pullback.fst B₁.I.blowupMap p
      = F.imageι ≫ pullback.snd p B₁.I.blowupMap := by
    rw [hidef, Category.assoc, hτfst]
  set f' : (B₁.I.blowupMap ⁻¹ᵁ U).toScheme ⟶ F.image := inv s ≫ F.toImage with hf'def
  have hf'i : f' ≫ i = baseChangeSection f hf B₁ := by
    simp only [hf'def, hidef, Category.assoc, Scheme.Hom.toImage_imageι_assoc, ← hbcs,
      IsIso.inv_hom_id_assoc]
  -- the hypotheses of Case 3 over the blow-up
  haveI : QuasiCompact B₁.I.blowupMap := B₁.quasiCompact_blowupMap
  haveI : CompactSpace B₁.I.blowup :=
    QuasiCompact.compactSpace_of_compactSpace B₁.I.blowupMap
  haveI : IsSeparated B₁.I.blowupMap := B₁.isProper_blowupMap.toIsSeparated
  haveI : QuasiSeparatedSpace B₁.I.blowup :=
    quasiSeparatedSpace_of_quasiSeparated B₁.I.blowupMap
  haveI : CompactSpace F.image :=
    QuasiCompact.compactSpace_of_compactSpace (F.imageι ≫ pullback.snd p B₁.I.blowupMap)
  haveI : QuasiSeparatedSpace F.image :=
    quasiSeparatedSpace_of_quasiSeparated (F.imageι ≫ pullback.snd p B₁.I.blowupMap)
  have hf'p : f' ≫ (F.imageι ≫ pullback.snd p B₁.I.blowupMap) = (B₁.I.blowupMap ⁻¹ᵁ U).ι := by
    rw [← hi, ← Category.assoc, hf'i, baseChangeSection_comp_fst]
  have hf'c : IsClosed (((F.imageι ≫ pullback.snd p B₁.I.blowupMap)
      ⁻¹ᵁ (B₁.I.blowupMap ⁻¹ᵁ V)).ι ⁻¹' Set.range f') := by
    have hbc := B₁.isClosed_preimage_range_baseChangeSection f hf hfc
    set O : (pullback B₁.I.blowupMap p : Scheme.{u}).Opens :=
      pullback.fst B₁.I.blowupMap p ⁻¹ᵁ (B₁.I.blowupMap ⁻¹ᵁ V) with hOdef
    have hpre : (F.imageι ≫ pullback.snd p B₁.I.blowupMap) ⁻¹ᵁ (B₁.I.blowupMap ⁻¹ᵁ V)
        = i ⁻¹ᵁ O := by
      rw [hOdef, ← hi, Scheme.Hom.comp_preimage]
    have hrng : ⇑i ⁻¹' Set.range (baseChangeSection f hf B₁) = Set.range f' := by
      rw [← hf'i]
      simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
      exact Set.preimage_image_eq _ i.isClosedEmbedding.injective
    have hset : ⇑(i ⁻¹ᵁ O).ι ⁻¹' Set.range f'
        = ⇑(i ∣_ O) ⁻¹' (⇑O.ι ⁻¹' Set.range (baseChangeSection f hf B₁)) := by
      have h := congrArg
        (fun t : (i ⁻¹ᵁ O).toScheme ⟶ (pullback B₁.I.blowupMap p : Scheme.{u}) =>
          ⇑t ⁻¹' Set.range (baseChangeSection f hf B₁)) (morphismRestrict_ι i O).symm
      simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp] at h
      rw [← hrng]
      exact h
    rw [hpre, hset]
    exact hbc.preimage (i ∣_ O).continuous
  -- **Steps 4 and 5**: base change along the blow-up, then replace the target by the image.
  refine exists_isAdmissible_extend_partialSection_of_blowup f hf B₁ ?_
  rw [← hf'i]
  -- **Step 1**: Case 3, applied to the quasi-affine morphism `F(U)‾ ⟶ X̃`.
  exact exists_isAdmissible_extend_partialSection_of_isClosedImmersion i hi f'
    (exists_isAdmissible_extend_of_isQuasiAffineHom_of_le
      (B₁.preimage_blowupMap_mono hUV) (B₁.isCompact_coe_preimage_blowupMap hU)
      (B₁.isCompact_coe_preimage_blowupMap hV) f' hf'p hf'c)

end AlgebraicGeometry
