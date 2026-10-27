/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FiniteRingSectionDeformation
import Sheaf.Paper.SectionReesBaseChangeEtale

/-! # Normal cones under base change of closed smooth sections

Source: latest blueprint, smooth-purity base-change factors, proof (1).
(blueprint: lem-sp-finite-section-integrated-specialization-normal-exchange).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

-- The original statement omitted hs and hs'. Geometry does not assert these
-- section equations; they are required by the source and already held by the caller.
/-- The geometric normal-cone exchange supplied by an arbitrary Cartesian section square.
Source: extended-Rees base-change compatibility and the homogeneous normal-cone comparison.
(blueprint: lem-sp-finite-section-integrated-specialization-normal-exchange).
This is the normal-fibre component used by the specialization and integration squares.

Proof: recover smoothness, separatedness and quasi-compactness of g by pulling the
geometric deformation back to t=1. The existing section Rees base-change theorem supplies
the Cartesian normal map for the canonical pullback and its compatibility with zero
sections. Identify the given Cartesian square with that pullback by its universal
property. The section equations identify the two centres. Apply the existing etale-pair
Rees theorem to this isomorphism to obtain an isomorphism of normal cones preserving
zero sections. Identify the normal maps in its compatibility data by cancellation of
the closed zero-fibre immersions. Paste the two normal squares and compose their
zero-section equations. No flatness of the base map is used. -/
theorem normalExchange_exists
    {V S V' S' : Scheme.{u}} [IsNoetherian S] [IsNoetherian S']
    (g : V ⟶ S) (g' : V' ⟶ S')
    (s : S ⟶ V) (s' : S' ⟶ V') [IsClosedImmersion s] [IsClosedImmersion s']
    (hs : s ≫ g = 𝟙 S) (hs' : s' ≫ g' = 𝟙 S')
    (b : S' ⟶ S) (q : V' ⟶ V) (cart : IsPullback q g' g b)
    (hsec : s' ≫ q = b ≫ s)
    (d : ℕ) [FiniteRingSectionDeformation.Geometry d g s]
    [FiniteRingSectionDeformation.Geometry d g' s'] :
    ∃ (ν : s'.ker.normalCone ⟶ s.ker.normalCone),
      IsPullback ν (Scheme.Hom.normalConeProj g' s')
        (Scheme.Hom.normalConeProj g s) b ∧
      s'.normalConeZeroSection ≫ ν = b ≫ s.normalConeZeroSection := by
  have hpb := Scheme.Hom.isPullback_deformationSpaceOneFibre g s
  have : SmoothOfRelativeDimension d g :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := d)).of_isPullback
      hpb inferInstance
  have : IsSeparated g := MorphismProperty.of_isPullback (P := @IsSeparated)
    hpb inferInstance
  have : QuasiCompact g := MorphismProperty.of_isPullback (P := @QuasiCompact)
    hpb inferInstance
  have : Smooth g := SmoothOfRelativeDimension.smooth d g
  obtain ⟨s₀, hc₀, w₀, hs₀, _, H₀, _, ν₀, hν₀, sq₀⟩ :=
    SectionReesBaseChange.base_change d g s hs b
  subst s₀
  let s₀ := Scheme.Hom.baseChangeSection g s hs b
  have := hc₀
  have hs₀ : s₀ ≫ pullback.snd g b = 𝟙 S' :=
    Scheme.Hom.baseChangeSection_snd g s hs b
  let e := cart.isoPullback
  have hef : e.hom ≫ pullback.fst g b = q := cart.isoPullback_hom_fst
  have he : e.hom ≫ pullback.snd g b = g' := cart.isoPullback_hom_snd
  have w : s' ≫ e.hom = s₀ := by
    apply pullback.hom_ext
    · simpa only [Category.assoc, hef] using hsec.trans w₀.symm
    · simpa only [Category.assoc, he] using hs'.trans hs₀.symm
  have centres : IsPullback s' (𝟙 S') e.hom s₀ :=
    IsPullback.of_vert_isIso (CommSq.mk (by simpa using w))
  obtain ⟨_, _, H₁, _, ν₁, hν₁, hIso⟩ :=
    SectionReesBaseChange.etale d (pullback.snd g b) s₀ hs₀ e.hom s'
      (by rw [← Category.assoc, w, hs₀]) (by simpa using w) centres
  obtain ⟨μ₀, _, _, hμ₀, _, hz₀, _⟩ := H₀.2.2.2
  obtain ⟨μ₁, _, _, hμ₁, hp₁, hz₁, _⟩ := H₁.2.2.2
  have : Mono s.ker.normalConeToDeformationSpace := by
    have : IsClosedImmersion s.ker.normalConeToDeformationSpace :=
      MorphismProperty.of_isPullback (P := @IsClosedImmersion)
        (Scheme.Hom.isPullback_normalConeToDeformationSpace g s).flip inferInstance
    infer_instance
  have : Mono s₀.ker.normalConeToDeformationSpace := by
    have : IsClosedImmersion s₀.ker.normalConeToDeformationSpace :=
      MorphismProperty.of_isPullback (P := @IsClosedImmersion)
        (Scheme.Hom.isPullback_normalConeToDeformationSpace (pullback.snd g b) s₀).flip
        inferInstance
    infer_instance
  have eq₀ : μ₀ = ν₀ := (cancel_mono s.ker.normalConeToDeformationSpace).mp
    (hμ₀.trans hν₀.symm)
  have eq₁ : μ₁ = ν₁ := (cancel_mono s₀.ker.normalConeToDeformationSpace).mp
    (hμ₁.trans hν₁.symm)
  rw [eq₀] at hz₀
  rw [eq₁, he] at hp₁
  rw [eq₁] at hz₁
  have := hIso
  have sq₁ : IsPullback ν₁ (Scheme.Hom.normalConeProj g' s')
      (Scheme.Hom.normalConeProj (pullback.snd g b) s₀) (𝟙 S') :=
    IsPullback.of_horiz_isIso (CommSq.mk hp₁)
  refine ⟨ν₁ ≫ ν₀, ?_, ?_⟩
  · simpa only [Category.id_comp] using sq₁.paste_horiz sq₀
  · rw [← Category.assoc, hz₁, Category.id_comp, hz₀]


end AlgebraicGeometry.Etale.FiniteSmoothPurity
