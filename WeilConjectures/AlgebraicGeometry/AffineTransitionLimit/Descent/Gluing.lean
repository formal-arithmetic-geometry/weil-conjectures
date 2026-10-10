/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.AffineTransitionLimit.Descent.DescendsToStage
public import WeilConjectures.Mathlib.Algebra.Category.Ring.FilteredColimits
public import WeilConjectures.Mathlib.Algebra.Category.Ring.FinitePresentation
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.Gluing
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
public import WeilConjectures.Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme

/-!
# Gluing finite-stage models along two opens

If a scheme over a cofiltered limit is covered by two opens with quasi-compact intersection, each
of which descends to a finite stage, then it descends to a finite stage
(`AlgebraicGeometry.DescendsToStage.of_sup_eq_top`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry
section FinitePresentationDescent
section Descent

set_option backward.defeqAttrib.useBackward true
variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} {c : Cone D} (hc : IsLimit c)
  [IsCofiltered I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]

include hc in
/-- (Implementation) **The two-open gluing step**: if a scheme over the limit is covered by
two opens with quasi-compact intersection, each of which descends to a finite stage, then it
descends to a finite stage. -/
lemma DescendsToStage.of_sup_eq_top {Z : Scheme.{u}} (gZ : Z ⟶ c.pt) (U V : Z.Opens)
    (hUV : U ⊔ V = ⊤) (hWc : IsCompact ((U ⊓ V : Z.Opens) : Set Z))
    (hU : DescendsToStage D c (U.ι ≫ gZ)) (hV : DescendsToStage D c (V.ι ≫ gZ)) :
    DescendsToStage D c gZ := by
  obtain ⟨k₁, hU⟩ := hU
  obtain ⟨k₂, hV⟩ := hV
  -- the intersection is quasi-compact in each of the two charts
  have hWU : IsCompact ((U.ι ⁻¹ᵁ V : U.toScheme.Opens) : Set U.toScheme) := by
    have he : (U.ι ⁻¹ᵁ V : U.toScheme.Opens) = U.ι ⁻¹ᵁ (U ⊓ V) := by
      rw [Scheme.Hom.preimage_inf, Scheme.Opens.ι_preimage_self, top_inf_eq]
    rw [he]
    refine U.ι.isOpenEmbedding.isInducing.isCompact_preimage' hWc ?_
    rw [Scheme.Opens.range_ι]
    exact inf_le_left
  have hWV : IsCompact ((V.ι ⁻¹ᵁ U : V.toScheme.Opens) : Set V.toScheme) := by
    have he : (V.ι ⁻¹ᵁ U : V.toScheme.Opens) = V.ι ⁻¹ᵁ (U ⊓ V) := by
      rw [Scheme.Hom.preimage_inf, Scheme.Opens.ι_preimage_self, inf_top_eq]
    rw [he]
    refine V.ι.isOpenEmbedding.isInducing.isCompact_preimage' hWc ?_
    rw [Scheme.Opens.range_ι]
    exact inf_le_right
  -- descend the intersection inside both charts, over a common stage
  obtain ⟨k₃, hU⟩ := exists_descendsAtWithOpen hc hU _ hWU
  obtain ⟨k₄, hV⟩ := exists_descendsAtWithOpen hc hV _ hWV
  replace hU := hU.mono (IsCofiltered.minToLeft k₃ k₄)
  replace hV := hV.mono (IsCofiltered.minToRight k₃ k₄)
  set k := IsCofiltered.min k₃ k₄ with hk
  obtain ⟨YU, pU, hUh, OU, hpU, hcU, hqU, HU, hOUc, hOU⟩ := hU
  obtain ⟨YV, pV, hVh, OV, hpV, hcV, hqV, HV, hOVc, hOV⟩ := hV
  have := hpU; have := hcU; have := hqU; have := hpV; have := hcV; have := hqV
  have : CompactSpace OU.toScheme := isCompact_iff_compactSpace.mp hOUc
  have : CompactSpace OV.toScheme := isCompact_iff_compactSpace.mp hOVc
  have : QuasiSeparatedSpace OU.toScheme :=
    QuasiSeparatedSpace.of_isOpenEmbedding OU.ι.isOpenEmbedding
  have : QuasiSeparatedSpace OV.toScheme :=
    QuasiSeparatedSpace.of_isOpenEmbedding OV.ι.isOpenEmbedding
  -- the two descended models of the intersection
  have hrangeU : (Scheme.Opens.infHomLeft U V).opensRange = U.ι ⁻¹ᵁ V := by
    rw [Scheme.opensRange_homOfLE, Scheme.Hom.preimage_inf, Scheme.Opens.ι_preimage_self,
      top_inf_eq]
  have hrangeV : (Scheme.Opens.infHomRight U V).opensRange = V.ι ⁻¹ᵁ U := by
    rw [Scheme.opensRange_homOfLE, Scheme.Hom.preimage_inf, Scheme.Opens.ι_preimage_self,
      inf_top_eq]
  have hsubU : Set.range (Scheme.Opens.infHomLeft U V ≫ hUh) ⊆ Set.range OU.ι := by
    rintro - ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    change hUh ((Scheme.Opens.infHomLeft U V) x) ∈ OU
    have : (Scheme.Opens.infHomLeft U V) x ∈ hUh ⁻¹ᵁ OU := by
      rw [hOU, ← hrangeU]
      exact ⟨x, rfl⟩
    exact this
  have hsubV : Set.range (Scheme.Opens.infHomRight U V ≫ hVh) ⊆ Set.range OV.ι := by
    rintro - ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    change hVh ((Scheme.Opens.infHomRight U V) x) ∈ OV
    have : (Scheme.Opens.infHomRight U V) x ∈ hVh ⁻¹ᵁ OV := by
      rw [hOV, ← hrangeV]
      exact ⟨x, rfl⟩
    exact this
  set aU₀ : (U ⊓ V : Z.Opens).toScheme ⟶ OU.toScheme :=
    IsOpenImmersion.lift OU.ι (Scheme.Opens.infHomLeft U V ≫ hUh) hsubU with haU₀
  set aV₀ : (U ⊓ V : Z.Opens).toScheme ⟶ OV.toScheme :=
    IsOpenImmersion.lift OV.ι (Scheme.Opens.infHomRight U V ≫ hVh) hsubV with haV₀
  have HaU : IsPullback aU₀ (Scheme.Opens.infHomLeft U V) OU.ι hUh :=
    IsOpenImmersion.isPullback _ _ _ _ (IsOpenImmersion.lift_fac _ _ hsubU).symm
      (by rw [Scheme.Opens.opensRange_ι, hOU, hrangeU])
  have HaV : IsPullback aV₀ (Scheme.Opens.infHomRight U V) OV.ι hVh :=
    IsOpenImmersion.isPullback _ _ _ _ (IsOpenImmersion.lift_fac _ _ hsubV).symm
      (by rw [Scheme.Opens.opensRange_ι, hOV, hrangeV])
  have HWU : IsPullback aU₀ ((U ⊓ V : Z.Opens).ι ≫ gZ) (OU.ι ≫ pU) (c.π.app k) := by
    have h := HaU.paste_vert HU
    rwa [← Category.assoc, Scheme.homOfLE_ι] at h
  have HWV : IsPullback aV₀ ((U ⊓ V : Z.Opens).ι ≫ gZ) (OV.ι ≫ pV) (c.π.app k) := by
    have h := HaV.paste_vert HV
    rwa [← Category.assoc, Scheme.homOfLE_ι] at h
  -- the two models of the intersection agree at a later stage
  obtain ⟨k', f', hiso⟩ := exists_iso_of_isPullback hc HWU HWV
  -- base change everything to that stage
  set YU' := pullback pU (D.map f') with hYU'
  set YV' := pullback pV (D.map f') with hYV'
  set pU' : YU' ⟶ D.obj k' := pullback.snd pU (D.map f') with hpU'
  set pV' : YV' ⟶ D.obj k' := pullback.snd pV (D.map f') with hpV'
  set hU' : U.toScheme ⟶ YU' := isPullbackLift D c f' HU with hhU'
  set hV' : V.toScheme ⟶ YV' := isPullbackLift D c f' HV with hhV'
  have HU' : IsPullback hU' (U.ι ≫ gZ) pU' (c.π.app k') := isPullback_isPullbackLift f' HU
  have HV' : IsPullback hV' (V.ι ≫ gZ) pV' (c.π.app k') := isPullback_isPullbackLift f' HV
  set OU' : YU'.Opens := pullback.fst pU (D.map f') ⁻¹ᵁ OU with hOU'
  set OV' : YV'.Opens := pullback.fst pV (D.map f') ⁻¹ᵁ OV with hOV'
  have HqU : IsPullback (pullback.fst pU (D.map f') ∣_ OU) (OU'.ι ≫ pU') (OU.ι ≫ pU)
      (D.map f') :=
    (isPullback_morphismRestrict (pullback.fst pU (D.map f')) OU).paste_vert
      (IsPullback.of_hasPullback pU (D.map f'))
  have HqV : IsPullback (pullback.fst pV (D.map f') ∣_ OV) (OV'.ι ≫ pV') (OV.ι ≫ pV)
      (D.map f') :=
    (isPullback_morphismRestrict (pullback.fst pV (D.map f')) OV).paste_vert
      (IsPullback.of_hasPullback pV (D.map f'))
  set h₁' : (U ⊓ V : Z.Opens).toScheme ⟶ OU'.toScheme :=
    HqU.lift aU₀ ((U ⊓ V : Z.Opens).ι ≫ gZ ≫ c.π.app k')
      (by rw [HWU.w]; simp only [Category.assoc]; rw [c.w f']) with hh₁'
  set h₂' : (U ⊓ V : Z.Opens).toScheme ⟶ OV'.toScheme :=
    HqV.lift aV₀ ((U ⊓ V : Z.Opens).ι ≫ gZ ≫ c.π.app k')
      (by rw [HWV.w]; simp only [Category.assoc]; rw [c.w f']) with hh₂'
  obtain ⟨e, he₁, he₂⟩ := hiso (h₁' := h₁') (h₂' := h₂') HqU
    (by rw [hh₁']; exact IsPullback.lift_fst ..)
    (by rw [hh₁', IsPullback.lift_snd, Category.assoc]) HqV
    (by rw [hh₂']; exact IsPullback.lift_fst ..)
    (by rw [hh₂', IsPullback.lift_snd, Category.assoc])
  -- glue the two charts along the descended intersection
  have hOU'c : IsCompact ((OU' : YU'.Opens) : Set YU') := by
    have : QuasiCompact (pullback.fst pU (D.map f')) :=
      MorphismProperty.pullback_fst _ _ inferInstance
    rw [hOU']
    exact QuasiCompact.isCompact_preimage _ OU.isOpen hOUc
  have : CompactSpace ↥(OU'.toScheme) := isCompact_iff_compactSpace.mp hOU'c
  have hcomm : OU'.ι ≫ pU' = (e.hom ≫ OV'.ι) ≫ pV' := by rw [Category.assoc, he₁]
  have hpreU : hU' ⁻¹ᵁ OU' = U.ι ⁻¹ᵁ V := by
    rw [hOU', ← Scheme.Hom.comp_preimage, hhU', isPullbackLift_fst, hOU]
  have hpreV : hV' ⁻¹ᵁ OV' = V.ι ⁻¹ᵁ U := by
    rw [hOV', ← Scheme.Hom.comp_preimage, hhV', isPullbackLift_fst, hOV]
  have hcommU : Scheme.Opens.infHomLeft U V ≫ hU' = h₁' ≫ OU'.ι := by
    apply pullback.hom_ext
    · rw [Category.assoc, hhU', isPullbackLift_fst, Category.assoc,
        ← morphismRestrict_ι (pullback.fst pU (D.map f')) OU, ← Category.assoc, hh₁',
        IsPullback.lift_fst, haU₀, IsOpenImmersion.lift_fac]
    · rw [Category.assoc, hhU', isPullbackLift_snd, Category.assoc]
      change _ = h₁' ≫ OU'.ι ≫ pU'
      rw [← Category.assoc, hh₁', IsPullback.lift_snd, Category.assoc,
        ← Category.assoc (Scheme.Opens.infHomLeft U V), Scheme.homOfLE_ι]
  have hcommV' : Scheme.Opens.infHomRight U V ≫ hV' = h₂' ≫ OV'.ι := by
    apply pullback.hom_ext
    · rw [Category.assoc, hhV', isPullbackLift_fst, Category.assoc,
        ← morphismRestrict_ι (pullback.fst pV (D.map f')) OV, ← Category.assoc, hh₂',
        IsPullback.lift_fst, haV₀, IsOpenImmersion.lift_fac]
    · rw [Category.assoc, hhV', isPullbackLift_snd, Category.assoc]
      change _ = h₂' ≫ OV'.ι ≫ pV'
      rw [← Category.assoc, hh₂', IsPullback.lift_snd, Category.assoc,
        ← Category.assoc (Scheme.Opens.infHomRight U V), Scheme.homOfLE_ι]
  have hcommV : Scheme.Opens.infHomRight U V ≫ hV' = h₁' ≫ e.hom ≫ OV'.ι := by
    rw [← Category.assoc, he₂, hcommV']
  have HsqU : IsPullback h₁' (Scheme.Opens.infHomLeft U V) OU'.ι hU' :=
    IsOpenImmersion.isPullback _ _ _ _ hcommU
      (by rw [Scheme.Opens.opensRange_ι, hpreU, hrangeU])
  have HsqV : IsPullback h₁' (Scheme.Opens.infHomRight U V) (e.hom ≫ OV'.ι) hV' :=
    IsOpenImmersion.isPullback _ _ _ _ hcommV
      (by
        rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Opens.opensRange_ι, hpreV, hrangeV])
  -- the glued finite-stage model
  have hf : h₁' ≫ OU'.ι = Scheme.Opens.infHomLeft U V ≫ hU' := hcommU.symm
  have hg : h₁' ≫ (e.hom ≫ OV'.ι) = Scheme.Opens.infHomRight U V ≫ hV' := hcommV.symm
  set p : pushout OU'.ι (e.hom ≫ OV'.ι) ⟶ D.obj k' := pushout.desc pU' pV' hcomm with hp
  set ρ := pushout.map (Scheme.Opens.infHomLeft U V)
    (Scheme.Opens.infHomRight U V) OU'.ι (e.hom ≫ OV'.ι) hU' hV' h₁'
    hf.symm hg.symm with hρ
  have hchartU := isPullback_pushout_map_inl_of_isPullback OU'.ι (e.hom ≫ OV'.ι)
    (Scheme.Opens.infHomLeft U V) (Scheme.Opens.infHomRight U V)
    hU' hV' h₁' hf hg HsqV
  have hchartV := isPullback_pushout_map_inr_of_isPullback OU'.ι (e.hom ≫ OV'.ι)
    (Scheme.Opens.infHomLeft U V) (Scheme.Opens.infHomRight U V)
    hU' hV' h₁' hf hg HsqU
  have hw : ρ ≫ p = (pushoutOpensDesc U V ≫ gZ) ≫ c.π.app k' := by
    apply pushout.hom_ext
    · rw [← Category.assoc, hρ, pushout.inl_desc, Category.assoc, hp, pushout.inl_desc]
      have hw' := HU'.w
      simp only [Category.assoc] at hw' ⊢
      rw [inl_pushoutOpensDesc_assoc]
      exact hw'
    · rw [← Category.assoc, hρ, pushout.inr_desc, Category.assoc, hp, pushout.inr_desc]
      have hw' := HV'.w
      simp only [Category.assoc] at hw' ⊢
      rw [inr_pushoutOpensDesc_assoc]
      exact hw'
  have hmain : IsPullback ρ (pushoutOpensDesc U V ≫ gZ) p (c.π.app k') := by
    refine isPullback_of_opensRange_sup_eq_top hw (pushout.inl OU'.ι (e.hom ≫ OV'.ι))
      (pushout.inr OU'.ι (e.hom ≫ OV'.ι))
      (opensRange_pushout_inl_sup_opensRange_pushout_inr OU'.ι (e.hom ≫ OV'.ι))
      hchartU hchartV ?_ ?_
    · rw [inl_pushoutOpensDesc_assoc, hp, pushout.inl_desc]
      exact HU'
    · rw [inr_pushoutOpensDesc_assoc, hp, pushout.inr_desc]
      exact HV'
  have := isIso_pushoutOpensDesc U V hUV
  refine ⟨k', pushout OU'.ι (e.hom ≫ OV'.ι), p, inv (pushoutOpensDesc U V) ≫ ρ,
    IsZariskiLocalAtSource.pushout_desc OU'.ι (e.hom ≫ OV'.ι) hcomm inferInstance inferInstance,
    inferInstance,
    quasiSeparatedSpace_pushout OU'.ι (e.hom ≫ OV'.ι), ?_⟩
  have hiso : IsPullback (inv (pushoutOpensDesc U V)) gZ (pushoutOpensDesc U V ≫ gZ)
      (𝟙 c.pt) := IsPullback.of_horiz_isIso ⟨by simp⟩
  simpa using hiso.paste_horiz hmain

end Descent

end FinitePresentationDescent

end AlgebraicGeometry
