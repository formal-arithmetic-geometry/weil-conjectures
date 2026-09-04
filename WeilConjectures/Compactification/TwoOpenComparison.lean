/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Compactification.IsomorphismNearClosure
public import WeilConjectures.Compactification.TwoOpenSetup
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!

# The comparison space of the two-open compactification theorem

This file builds the comparison layer of the two-open compactification theorem,
following the blueprint chapter "Nagata compactification", section "The two-open
compactification theorem" (`def:nagata-two-open-comparison-space` through
`lemma:nagata-one-valuation-avoids-boundary`):

Given two sides `σ₁ : CompactifiedProperExtension u O₁` and `σ₂ : CompactifiedProperExtension u O₂`,

- `AlgebraicGeometry.CompactifiedProperExtension.comparisonMap`: the canonical morphism
  `V₁ ×_U V₂ ⟶ X₁ ×_S X₂` (blueprint: `def:nagata-two-open-comparison-space`);
- `AlgebraicGeometry.CompactifiedProperExtension.comparisonSpace`: its scheme-theoretic image `X₁₂`,
  with the two proper projections `comparisonFst`/`comparisonSnd` (blueprint:
  `lemma:nagata-comparison-projections-proper`);
- `AlgebraicGeometry.CompactifiedProperExtension.KeyDisjoint`: the **key boundary disjointness**
  `X₁₂ ∩ (Z̄₁,₂ ×_S Z̄₂,₁) = ∅` in pointwise form (blueprint:
  `lemma:nagata-key-boundary-disjointness`);
- `AlgebraicGeometry.CompactifiedProperExtension.KeyDisjoint.avoids`: key disjointness
  implies that of any pair of valuation-ring extensions of a common generic point of
  `O₁ ∩ O₂` to the two ambient models, at least one avoids its forbidden boundary
  (blueprint:
  `lemma:nagata-valuation-pair-factors-comparison`,
  `lemma:nagata-valuation-open-closed-point`,
  `lemma:nagata-one-valuation-avoids-boundary`);
- `AlgebraicGeometry.TwoOpenPreparation`: the bundled output of the comparison layer,
  consumed by the final assembly of the two-open theorem;
- `AlgebraicGeometry.nonempty_twoOpenPreparation`: existence. The construction of a
  key-disjoint prepared pair (`exists_prepared_keyDisjoint_compactifiedProperExtension`) is the
  improved-comparison chain of the blueprint
  (`lemma:nagata-comparison-restrict-proper-open`,
  `def:nagata-two-open-improved-comparison` via Stacks Project Tag 0F3W,
  `lemma:nagata-comparison-boundary-density`,
  `lemma:nagata-key-boundary-disjointness`); it consumes the modification input
  `exists_admissibleBlowup_isIso_strictTransformMap_near_closure` and therefore,
  through it, Stacks Tag 081S — see the module docstrings of
  `WeilConjectures.Compactification.IsomorphismNearClosure` and
  `WeilConjectures.Compactification.EliminationOfIndeterminacy`.

## The improved comparison

`AlgebraicGeometry.exists_admissibleBlowup_comparisonBoundary_subset_selfBoundary` is
the geometric core of the file. Its ingredients, all proved here, are:

- `CompactifiedProperExtension.range_toImage_comparisonMap`
  (`lemma:nagata-comparison-restrict-proper-open`): over the proper-extension open
  `V₁` the comparison space is the fibre product `V₁ ×_U V₂` itself. The comparison
  morphism is an immersion, being the base change of the diagonal of `u` followed by
  an open immersion, and it is proper over `V₁`, so its range is closed there;
- `CompactifiedProperExtension.isIso_comparisonFst_restrict_isoOpen`: the first
  comparison projection is an isomorphism over `CompactifiedProperExtension.isoOpen`,
  the image in `X₁` of the locus of `V₁` lying above `O₂`. Indeed `ψ₂` is an isomorphism
  over `O₂` and, over `V₁`, the first projection is its base change. That open contains
  the forbidden boundary locus
  `Z₁,₂`, because `U ∖ O₁ ⊆ O₂`;
- `CompactifiedProperExtension.injOn_comparisonFst_admissibleBlowup`: after a
  `V₁`-admissible blow-up the comparison space of the improved pair is a closed subscheme
  of the strict transform of the old comparison space
  (`CompactifiedProperExtension.strictTransformComparisonι`), so
  the improved first projection is injective wherever the strict-transform projection
  is an isomorphism. This is the point at which Stacks Project Tag 0F3W enters;
- `CompactifiedProperExtension.comparisonBoundary_subset_preimage_selfBoundary` is the density
  criterion `lemma:nagata-comparison-boundary-density`: controlling the second
  projection on a subset whose closure swallows the comparison boundary suffices,
  because the self boundary is itself a closure;
- `CompactifiedProperExtension.keyDisjoint_of_comparisonBoundary_subset` is
  `lemma:nagata-key-boundary-disjointness`: a comparison boundary landing in the self
  boundary `Z̄₂,₂` of a *prepared* second side cannot meet its forbidden boundary
  `Z̄₂,₁`.

The closed immersion of the improved comparison space into the strict transform is
built directly from the universal property of the scheme-theoretic image, so Stacks
Project Tag 0F3Y (`Scheme.Hom.ker_lift_admissibleBlowup`) is not used here.

-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits IsLocalRing

namespace AlgebraicGeometry

variable {U S : Scheme.{u}} {u : U ⟶ S} {O₁ O₂ : U.Opens}

namespace CompactifiedProperExtension

section Supplement

/-! ### Supplementary lemmas on a single compactified proper extension

These are recorded here rather than in
`WeilConjectures.Compactification.CompactifiedProperExtension` so that that file stays a
verbatim copy of the one carrying the structure to `master`. -/

variable {O : U.Opens} (σ : CompactifiedProperExtension u O)

/-- The embedded copy of `O` in the ambient model lies over `O` in `S`. -/
@[reassoc]
lemma υ_i_g : σ.υ ≫ σ.X.i ≫ σ.X.g = O.ι ≫ u := by
  rw [← σ.X.comm, ← Category.assoc, σ.υ_ψ]

/-- **The embedded copy of `O` is dense in the ambient model**: over a Noetherian base
the scheme-theoretic dominance of the structure implies topological dominance. -/
lemma dense_range_υ_i [IsNoetherian S] : Dense (Set.range (σ.υ ≫ σ.X.i)) := by
  have := σ.isNoetherian_Z
  have : IsSchemeTheoreticallyDominant (σ.υ ≫ σ.X.i).opensRange.ι :=
    (isSchemeTheoreticallyDominant_iff_opensRange_ι _).mp inferInstance
  have hd : Dense (Set.range (σ.υ ≫ σ.X.i).opensRange.ι) := Scheme.Hom.denseRange _
  simpa [Scheme.Opens.range_ι] using hd

/-- **The proper extension of a compactified proper extension over a Noetherian base is
Noetherian**: it is an open subscheme of the ambient model, which is proper over `S`. -/
lemma isNoetherian_V [IsNoetherian S] : IsNoetherian σ.V := by
  have := σ.isNoetherian_Z
  have : IsLocallyNoetherian σ.V := LocallyOfFiniteType.isLocallyNoetherian σ.X.i
  have : CompactSpace (σ.X.i.opensRange : σ.X.Z.Opens) :=
    isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact _)
  have : CompactSpace σ.V := (Scheme.homeoOfIso σ.X.i.isoOpensRange).symm.compactSpace
  exact ⟨⟩

end Supplement

variable (σ₁ : CompactifiedProperExtension u O₁) (σ₂ : CompactifiedProperExtension u O₂)

/-- The canonical morphism `V₁ ×_U V₂ ⟶ X₁ ×_S X₂` from the fibre product of the two
proper extensions to the product of the two ambient models.
(Blueprint: `def:nagata-two-open-comparison-space`.) -/
def comparisonMap : pullback σ₁.ψ σ₂.ψ ⟶ pullback σ₁.X.g σ₂.X.g :=
  pullback.map σ₁.ψ σ₂.ψ σ₁.X.g σ₂.X.g σ₁.X.i σ₂.X.i u σ₁.X.comm σ₂.X.comm

/-- The **comparison space** `X₁₂`: the scheme-theoretic image of `V₁ ×_U V₂` in
`X₁ ×_S X₂`. (Blueprint: `def:nagata-two-open-comparison-space`.) -/
def comparisonSpace : Scheme.{u} := (comparisonMap σ₁ σ₂).image

/-- The first projection `X₁₂ ⟶ X₁` of the comparison space. -/
def comparisonFst : comparisonSpace σ₁ σ₂ ⟶ σ₁.X.Z :=
  (comparisonMap σ₁ σ₂).imageι ≫ pullback.fst σ₁.X.g σ₂.X.g

/-- The second projection `X₁₂ ⟶ X₂` of the comparison space. -/
def comparisonSnd : comparisonSpace σ₁ σ₂ ⟶ σ₂.X.Z :=
  (comparisonMap σ₁ σ₂).imageι ≫ pullback.snd σ₁.X.g σ₂.X.g

@[simp]
lemma comparisonFst_eq :
    comparisonFst σ₁ σ₂ = (comparisonMap σ₁ σ₂).imageι ≫ pullback.fst σ₁.X.g σ₂.X.g := rfl

@[simp]
lemma comparisonSnd_eq :
    comparisonSnd σ₁ σ₂ = (comparisonMap σ₁ σ₂).imageι ≫ pullback.snd σ₁.X.g σ₂.X.g := rfl

/-- **Properness of the comparison projections** (blueprint:
`lemma:nagata-comparison-projections-proper`): the projection `X₁₂ ⟶ X₁` is a closed
immersion followed by a base change of the proper structure morphism of `X₂`. -/
theorem isProper_comparisonFst : IsProper (comparisonFst σ₁ σ₂) := by
  have := σ₂.X.isProper
  rw [comparisonFst_eq]
  infer_instance

/-- **Properness of the comparison projections**, second projection: `X₁₂ ⟶ X₂` is a
closed immersion followed by a base change of the proper structure morphism of `X₁`. -/
theorem isProper_comparisonSnd : IsProper (comparisonSnd σ₁ σ₂) := by
  have := σ₁.X.isProper
  rw [comparisonSnd_eq]
  infer_instance

section ComparisonOverV

/-! ### The comparison space over the proper-extension open

Over `V₁ ⊆ X₁` the comparison space is the fibre product `V₁ ×_U V₂` itself, and over the
locus of `V₁ lying above `O₂` — where `ψ₂` is an isomorphism — the first comparison
projection is an isomorphism. This is the input of the improved comparison
(blueprint: `lemma:nagata-comparison-restrict-proper-open`). -/

/-- The two comparison projections lie over the same morphism to the base. -/
@[reassoc]
lemma comparisonFst_s : comparisonFst σ₁ σ₂ ≫ σ₁.X.g = comparisonSnd σ₁ σ₂ ≫ σ₂.X.g := by
  rw [comparisonFst_eq, comparisonSnd_eq, Category.assoc, Category.assoc, pullback.condition]

@[reassoc]
lemma comparisonMap_fst :
    comparisonMap σ₁ σ₂ ≫ pullback.fst σ₁.X.g σ₂.X.g = pullback.fst σ₁.ψ σ₂.ψ ≫ σ₁.X.i :=
  pullback.lift_fst _ _ _

@[reassoc]
lemma comparisonMap_snd :
    comparisonMap σ₁ σ₂ ≫ pullback.snd σ₁.X.g σ₂.X.g = pullback.snd σ₁.ψ σ₂.ψ ≫ σ₂.X.i :=
  pullback.lift_snd _ _ _

@[reassoc]
lemma toImage_comparisonFst :
    (comparisonMap σ₁ σ₂).toImage ≫ comparisonFst σ₁ σ₂ =
      pullback.fst σ₁.ψ σ₂.ψ ≫ σ₁.X.i := by
  rw [comparisonFst_eq, ← Category.assoc, Scheme.Hom.toImage_imageι, comparisonMap_fst]

@[reassoc]
lemma toImage_comparisonSnd :
    (comparisonMap σ₁ σ₂).toImage ≫ comparisonSnd σ₁ σ₂ =
      pullback.snd σ₁.ψ σ₂.ψ ≫ σ₂.X.i := by
  rw [comparisonSnd_eq, ← Category.assoc, Scheme.Hom.toImage_imageι, comparisonMap_snd]

lemma comparisonFst_toImage_apply (w : ↥(pullback σ₁.ψ σ₂.ψ)) :
    comparisonFst σ₁ σ₂ ((comparisonMap σ₁ σ₂).toImage w) =
      σ₁.X.i (pullback.fst σ₁.ψ σ₂.ψ w) :=
  calc comparisonFst σ₁ σ₂ ((comparisonMap σ₁ σ₂).toImage w)
      = ((comparisonMap σ₁ σ₂).toImage ≫ comparisonFst σ₁ σ₂) w :=
        (Scheme.Hom.comp_apply _ _ _).symm
    _ = (pullback.fst σ₁.ψ σ₂.ψ ≫ σ₁.X.i) w := by rw [toImage_comparisonFst]
    _ = σ₁.X.i (pullback.fst σ₁.ψ σ₂.ψ w) := Scheme.Hom.comp_apply _ _ _

lemma comparisonSnd_toImage_apply (w : ↥(pullback σ₁.ψ σ₂.ψ)) :
    comparisonSnd σ₁ σ₂ ((comparisonMap σ₁ σ₂).toImage w) =
      σ₂.X.i (pullback.snd σ₁.ψ σ₂.ψ w) :=
  calc comparisonSnd σ₁ σ₂ ((comparisonMap σ₁ σ₂).toImage w)
      = ((comparisonMap σ₁ σ₂).toImage ≫ comparisonSnd σ₁ σ₂) w :=
        (Scheme.Hom.comp_apply _ _ _).symm
    _ = (pullback.snd σ₁.ψ σ₂.ψ ≫ σ₂.X.i) w := by rw [toImage_comparisonSnd]
    _ = σ₂.X.i (pullback.snd σ₁.ψ σ₂.ψ w) := Scheme.Hom.comp_apply _ _ _

lemma ψ_pullback_fst_apply (w : ↥(pullback σ₁.ψ σ₂.ψ)) :
    σ₁.ψ (pullback.fst σ₁.ψ σ₂.ψ w) = σ₂.ψ (pullback.snd σ₁.ψ σ₂.ψ w) :=
  calc σ₁.ψ (pullback.fst σ₁.ψ σ₂.ψ w)
      = (pullback.fst σ₁.ψ σ₂.ψ ≫ σ₁.ψ) w := (Scheme.Hom.comp_apply _ _ _).symm
    _ = (pullback.snd σ₁.ψ σ₂.ψ ≫ σ₂.ψ) w := by rw [pullback.condition]
    _ = σ₂.ψ (pullback.snd σ₁.ψ σ₂.ψ w) := Scheme.Hom.comp_apply _ _ _

lemma range_comparisonMap_subset :
    Set.range ⇑(comparisonMap σ₁ σ₂) ⊆
      Set.range ⇑(pullback.fst σ₁.X.g σ₂.X.g ⁻¹ᵁ σ₁.X.i.opensRange).ι := by
  rw [Scheme.Opens.range_ι]
  rintro - ⟨w, rfl⟩
  have h : pullback.fst σ₁.X.g σ₂.X.g (comparisonMap σ₁ σ₂ w) ∈
      (σ₁.X.i.opensRange : Set σ₁.X.Z) := by
    rw [← Scheme.Hom.comp_apply, comparisonMap_fst, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  exact h

/-- The comparison morphism, viewed as a morphism into the locus of `X₁ ×_S X₂` over the
proper-extension open `V₁`. -/
def comparisonMapRestrict :
    pullback σ₁.ψ σ₂.ψ ⟶ (pullback.fst σ₁.X.g σ₂.X.g ⁻¹ᵁ σ₁.X.i.opensRange).toScheme :=
  IsOpenImmersion.lift (pullback.fst σ₁.X.g σ₂.X.g ⁻¹ᵁ σ₁.X.i.opensRange).ι (comparisonMap σ₁ σ₂)
    (range_comparisonMap_subset σ₁ σ₂)

@[reassoc (attr := simp)]
lemma comparisonMapRestrict_ι :
    comparisonMapRestrict σ₁ σ₂ ≫ (pullback.fst σ₁.X.g σ₂.X.g ⁻¹ᵁ σ₁.X.i.opensRange).ι =
      comparisonMap σ₁ σ₂ :=
  IsOpenImmersion.lift_fac _ _ _

lemma comparisonMapRestrict_fst :
    comparisonMapRestrict σ₁ σ₂ ≫ (pullback.fst σ₁.X.g σ₂.X.g ∣_ σ₁.X.i.opensRange) =
      pullback.fst σ₁.ψ σ₂.ψ ≫ σ₁.X.i.isoOpensRange.hom := by
  rw [← cancel_mono (σ₁.X.i.opensRange).ι, Category.assoc, morphismRestrict_ι,
    comparisonMapRestrict_ι_assoc, comparisonMap_fst, Category.assoc,
    Scheme.Hom.isoOpensRange_hom_ι]

/-- The comparison morphism is proper over `V₁`, since `V₁ ×_U V₂ ⟶ V₁` is a base change
of the proper morphism `ψ₂` and `X₁ ×_S X₂ ⟶ X₁` is separated. -/
instance isProper_comparisonMapRestrict : IsProper (comparisonMapRestrict σ₁ σ₂) := by
  have : IsProper (comparisonMapRestrict σ₁ σ₂ ≫
      (pullback.fst σ₁.X.g σ₂.X.g ∣_ σ₁.X.i.opensRange)) := by
    rw [comparisonMapRestrict_fst]
    infer_instance
  have : IsProper (pullback.fst σ₁.X.g σ₂.X.g) := inferInstance
  exact IsProper.of_comp _ (pullback.fst σ₁.X.g σ₂.X.g ∣_ σ₁.X.i.opensRange)

lemma preimage_range_comparisonMap :
    ⇑(pullback.fst σ₁.X.g σ₂.X.g ⁻¹ᵁ σ₁.X.i.opensRange).ι ⁻¹' Set.range ⇑(comparisonMap σ₁ σ₂) =
      Set.range ⇑(comparisonMapRestrict σ₁ σ₂) := by
  ext x
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w, (pullback.fst σ₁.X.g σ₂.X.g ⁻¹ᵁ σ₁.X.i.opensRange).ι.isOpenEmbedding.injective
      (by rw [← Scheme.Hom.comp_apply, comparisonMapRestrict_ι, hw])⟩
  · rintro ⟨w, rfl⟩
    exact ⟨w, by rw [← Scheme.Hom.comp_apply, comparisonMapRestrict_ι]⟩

/-- The comparison morphism factors as the base change of the diagonal of `u` followed
by the open immersion `V₁ ×_S V₂ ⟶ X₁ ×_S X₂`; both factors are immersions. -/
lemma comparisonMap_eq_mapDesc_comp :
    comparisonMap σ₁ σ₂ = pullback.mapDesc σ₁.ψ σ₂.ψ u ≫
      pullback.map (σ₁.ψ ≫ u) (σ₂.ψ ≫ u) σ₁.X.g σ₂.X.g σ₁.X.i σ₂.X.i (𝟙 S)
        ((Category.comp_id _).trans σ₁.X.comm) ((Category.comp_id _).trans σ₂.X.comm) := by
  apply pullback.hom_ext <;> simp [comparisonMap]

instance isImmersion_comparisonMap : IsImmersion (comparisonMap σ₁ σ₂) := by
  have : IsOpenImmersion
      (pullback.map (σ₁.ψ ≫ u) (σ₂.ψ ≫ u) σ₁.X.g σ₂.X.g σ₁.X.i σ₂.X.i (𝟙 S)
        ((Category.comp_id _).trans σ₁.X.comm) ((Category.comp_id _).trans σ₂.X.comm)) :=
    MorphismProperty.pullbackMap (P := @IsOpenImmersion) inferInstance inferInstance
      σ₁.X.comm σ₂.X.comm
  rw [comparisonMap_eq_mapDesc_comp]
  infer_instance

variable [IsNoetherian S]

instance quasiCompact_comparisonMap : QuasiCompact (comparisonMap σ₁ σ₂) := by
  have := σ₁.isNoetherian_Z
  have := σ₁.isNoetherian_V
  have : QuasiCompact (comparisonMap σ₁ σ₂ ≫ pullback.fst σ₁.X.g σ₂.X.g) := by
    rw [comparisonMap_fst]
    infer_instance
  have : QuasiSeparated (pullback.fst σ₁.X.g σ₂.X.g) := inferInstance
  exact QuasiCompact.of_comp _ (pullback.fst σ₁.X.g σ₂.X.g)

/-- **Restriction of the comparison image over the proper-extension open** (blueprint:
`lemma:nagata-comparison-restrict-proper-open`): the part of the comparison space lying
over `V₁` is exactly the image of `V₁ ×_U V₂`, which is an open subscheme of the
comparison space because the comparison morphism is a quasi-compact immersion. -/
theorem range_toImage_comparisonMap :
    Set.range ⇑(comparisonMap σ₁ σ₂).toImage =
      ⇑(comparisonFst σ₁ σ₂) ⁻¹' (σ₁.X.i.opensRange : Set σ₁.X.Z) := by
  apply subset_antisymm
  · rintro - ⟨w, rfl⟩
    refine Set.mem_preimage.mpr ?_
    rw [comparisonFst_toImage_apply]
    exact ⟨_, rfl⟩
  · have hsub := (comparisonMap σ₁ σ₂).preimage_subset_range_toImage_of_isClosed
      (W := pullback.fst σ₁.X.g σ₂.X.g ⁻¹ᵁ σ₁.X.i.opensRange) (by
        rw [preimage_range_comparisonMap]
        have h := (comparisonMapRestrict σ₁ σ₂).isClosedMap _ isClosed_univ
        rwa [Set.image_univ] at h)
    intro z hz
    refine hsub ?_
    have h : pullback.fst σ₁.X.g σ₂.X.g ((comparisonMap σ₁ σ₂).imageι z) ∈
        (σ₁.X.i.opensRange : Set σ₁.X.Z) := by
      rw [← Scheme.Hom.comp_apply, ← comparisonFst_eq]
      exact hz
    exact h

end ComparisonOverV

section ComparisonSection

/-- The canonical section of the base change `V₁ ×_U V₂ ⟶ V₁` over the locus of `V₁`
lying above `O₂`: there `ψ₂` is an isomorphism, with inverse the embedded copy `υ₂` of
`O₂` in `V₂`. -/
def fstSection : (σ₁.ψ ⁻¹ᵁ O₂).toScheme ⟶ pullback σ₁.ψ σ₂.ψ :=
  pullback.lift (σ₁.ψ ⁻¹ᵁ O₂).ι ((σ₁.ψ ∣_ O₂) ≫ σ₂.υ)
    (by rw [Category.assoc, σ₂.υ_ψ, morphismRestrict_ι])

@[reassoc (attr := simp)]
lemma fstSection_fst :
    fstSection σ₁ σ₂ ≫ pullback.fst σ₁.ψ σ₂.ψ = (σ₁.ψ ⁻¹ᵁ O₂).ι :=
  pullback.lift_fst _ _ _

/-- Every point of `V₁` lying over `O₂` is hit by the base change `V₁ ×_U V₂ ⟶ V₁`. -/
lemma preimage_subset_range_pullback_fst :
    ⇑σ₁.ψ ⁻¹' (O₂ : Set U) ⊆ Set.range ⇑(pullback.fst σ₁.ψ σ₂.ψ) := by
  intro v hv
  have hv' : v ∈ Set.range ⇑(σ₁.ψ ⁻¹ᵁ O₂).ι := by
    rw [Scheme.Opens.range_ι]
    exact hv
  obtain ⟨x, rfl⟩ := hv'
  exact ⟨fstSection σ₁ σ₂ x, by rw [← Scheme.Hom.comp_apply, fstSection_fst]⟩

instance isIso_pullback_fst_restrict :
    IsIso (pullback.fst σ₁.ψ σ₂.ψ ∣_ (σ₁.ψ ⁻¹ᵁ O₂)) :=
  isIso_morphismRestrict_pullback_fst σ₁.ψ σ₂.ψ O₂

instance isOpenImmersion_fstSection : IsOpenImmersion (fstSection σ₁ σ₂) := by
  have h : IsIso (pullback.fst σ₁.ψ σ₂.ψ ∣_ (σ₁.ψ ⁻¹ᵁ O₂).ι.opensRange) := by
    rw [Scheme.Opens.opensRange_ι]
    infer_instance
  exact isOpenImmersion_of_comp_eq _ _ (fstSection_fst σ₁ σ₂)

lemma range_fstSection :
    Set.range ⇑(fstSection σ₁ σ₂) =
      ⇑(pullback.fst σ₁.ψ σ₂.ψ) ⁻¹' (⇑σ₁.ψ ⁻¹' (O₂ : Set U)) := by
  have h : IsIso (pullback.fst σ₁.ψ σ₂.ψ ∣_ (σ₁.ψ ⁻¹ᵁ O₂).ι.opensRange) := by
    rw [Scheme.Opens.opensRange_ι]
    infer_instance
  rw [range_eq_preimage_range_of_comp_eq _ _ (fstSection_fst σ₁ σ₂),
    Scheme.Opens.range_ι]
  rfl

variable [IsNoetherian S]

/-- The copy of the locus of `V₁` above `O₂` inside the comparison space. -/
def comparisonSection : (σ₁.ψ ⁻¹ᵁ O₂).toScheme ⟶ comparisonSpace σ₁ σ₂ :=
  fstSection σ₁ σ₂ ≫ (comparisonMap σ₁ σ₂).toImage

instance isOpenImmersion_comparisonSection :
    IsOpenImmersion (comparisonSection σ₁ σ₂) := by
  rw [comparisonSection]
  infer_instance

omit [IsNoetherian S] in
@[reassoc]
lemma comparisonSection_comparisonFst :
    comparisonSection σ₁ σ₂ ≫ comparisonFst σ₁ σ₂ = (σ₁.ψ ⁻¹ᵁ O₂).ι ≫ σ₁.X.i := by
  rw [comparisonSection, Category.assoc, toImage_comparisonFst, ← Category.assoc,
    fstSection_fst]

instance isOpenImmersion_comparisonSection_comparisonFst :
    IsOpenImmersion (comparisonSection σ₁ σ₂ ≫ comparisonFst σ₁ σ₂) := by
  rw [comparisonSection_comparisonFst]
  infer_instance

/-- The open of `X₁` over which the first comparison projection is an isomorphism: the
image in `X₁` of the locus of `V₁` lying above `O₂`. -/
def isoOpen : σ₁.X.Z.Opens := (comparisonSection σ₁ σ₂ ≫ comparisonFst σ₁ σ₂).opensRange

omit [IsNoetherian S] in
lemma range_comparisonSection_comparisonFst :
    Set.range ⇑(comparisonSection σ₁ σ₂ ≫ comparisonFst σ₁ σ₂) =
      ⇑σ₁.X.i '' (⇑σ₁.ψ ⁻¹' (O₂ : Set U)) := by
  rw [comparisonSection_comparisonFst, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.range_comp, Scheme.Opens.range_ι]
  rfl

omit [IsNoetherian S] in
lemma isoOpen_eq_image : (isoOpen σ₁ σ₂ : Set σ₁.X.Z) = ⇑σ₁.X.i '' (⇑σ₁.ψ ⁻¹' (O₂ : Set U)) :=
  range_comparisonSection_comparisonFst σ₁ σ₂

lemma range_comparisonSection :
    Set.range ⇑(comparisonSection σ₁ σ₂) =
      ⇑(comparisonFst σ₁ σ₂) ⁻¹' Set.range ⇑(comparisonSection σ₁ σ₂ ≫ comparisonFst σ₁ σ₂) := by
  rw [range_comparisonSection_comparisonFst]
  apply subset_antisymm
  · rintro - ⟨x, rfl⟩
    refine Set.mem_preimage.mpr ?_
    rw [← Scheme.Hom.comp_apply, comparisonSection_comparisonFst, Scheme.Hom.comp_apply]
    refine ⟨(σ₁.ψ ⁻¹ᵁ O₂).ι x, ?_, rfl⟩
    have hx : (σ₁.ψ ⁻¹ᵁ O₂).ι x ∈
        ((σ₁.ψ ⁻¹ᵁ O₂ : σ₁.V.Opens) : Set σ₁.V) := by
      rw [← Scheme.Opens.range_ι]
      exact ⟨x, rfl⟩
    exact hx
  · intro z hz
    obtain ⟨v, hv, hvz⟩ := hz
    have hzV : z ∈ ⇑(comparisonFst σ₁ σ₂) ⁻¹' (σ₁.X.i.opensRange : Set σ₁.X.Z) := by
      rw [Set.mem_preimage, ← hvz]
      exact ⟨v, rfl⟩
    rw [← range_toImage_comparisonMap] at hzV
    obtain ⟨w, rfl⟩ := hzV
    have hfw : pullback.fst σ₁.ψ σ₂.ψ w = v := by
      apply σ₁.X.i.isOpenEmbedding.injective
      rw [← comparisonFst_toImage_apply, hvz]
    have hwmem : w ∈ Set.range ⇑(fstSection σ₁ σ₂) := by
      rw [range_fstSection, Set.mem_preimage, Set.mem_preimage, hfw]
      exact hv
    obtain ⟨x, rfl⟩ := hwmem
    refine ⟨x, ?_⟩
    change (fstSection σ₁ σ₂ ≫ (comparisonMap σ₁ σ₂).toImage) x = _
    exact Scheme.Hom.comp_apply _ _ _

/-- **The first comparison projection is an isomorphism over the locus above `O₂`**
(blueprint: part of `lemma:nagata-comparison-isIso-near-boundary`): over `O₂` the proper
extension `ψ₂` is an isomorphism, hence so is its base change `V₁ ×_U V₂ ⟶ V₁`, and the
comparison space agrees with `V₁ ×_U V₂` over `V₁`. -/
theorem isIso_comparisonFst_restrict_isoOpen :
    IsIso (comparisonFst σ₁ σ₂ ∣_ isoOpen σ₁ σ₂) :=
  isIso_morphismRestrict_opensRange_of_range_eq (comparisonFst σ₁ σ₂)
    (comparisonSection σ₁ σ₂) (range_comparisonSection σ₁ σ₂)

end ComparisonSection

/-- The **key boundary disjointness** (blueprint:
`lemma:nagata-key-boundary-disjointness`): no point of the comparison space projects
into the forbidden boundary on both sides, i.e.
`X₁₂ ∩ (Z̄₁,₂ ×_S Z̄₂,₁) = ∅` inside `X₁ ×_S X₂`. -/
def KeyDisjoint : Prop :=
  ∀ z : comparisonSpace σ₁ σ₂,
    comparisonFst σ₁ σ₂ z ∈ σ₁.forbiddenBoundary →
    comparisonSnd σ₁ σ₂ z ∉ σ₂.forbiddenBoundary

/-- The **comparison boundary** of the pair `(σ₁, σ₂)`: the locus of the comparison
space lying over the forbidden boundary `Z̄₁,₂` of the first side. Key boundary
disjointness is the assertion that its second projection avoids the forbidden boundary
of the second side. (Blueprint: `lemma:nagata-comparison-boundary-density`.) -/
def comparisonBoundary : Set (comparisonSpace σ₁ σ₂) :=
  comparisonFst σ₁ σ₂ ⁻¹' σ₁.forbiddenBoundary

lemma isClosed_comparisonBoundary : IsClosed (comparisonBoundary σ₁ σ₂) :=
  isClosed_closure.preimage (comparisonFst σ₁ σ₂).continuous

variable {σ₁ σ₂} in
lemma mem_comparisonBoundary_iff {z : comparisonSpace σ₁ σ₂} :
    z ∈ comparisonBoundary σ₁ σ₂ ↔
      comparisonFst σ₁ σ₂ z ∈ σ₁.forbiddenBoundary :=
  Iff.rfl

variable {σ₁ σ₂} in
/-- **Key boundary disjointness from the self boundary** (blueprint:
`lemma:nagata-key-boundary-disjointness`): if the second projection of the comparison
boundary lands in the self boundary `Z̄₂,₂` of the second side, then key disjointness
holds, because a prepared side has disjoint self and forbidden boundaries.

This is the final link of the improved-comparison chain, and the only one of its links
that needs neither Stacks Project Tag 0F3W nor Tag 0F3Y. -/
theorem keyDisjoint_of_comparisonBoundary_subset (h₂ : σ₂.Prepared O₁)
    (h : comparisonBoundary σ₁ σ₂ ⊆ comparisonSnd σ₁ σ₂ ⁻¹' σ₂.selfBoundary O₁) :
    KeyDisjoint σ₁ σ₂ :=
  fun _ hz ↦ Set.disjoint_left.mp h₂ (h hz)

variable {σ₁ σ₂} in
/-- **The comparison boundary density criterion** (blueprint:
`lemma:nagata-comparison-boundary-density`): it suffices to control the second
projection on a subset `D` in which the comparison boundary is contained after taking
closures. The locus where the second projection lands in the self boundary is closed,
since the self boundary is a closure, so it swallows `closure D`. -/
theorem comparisonBoundary_subset_preimage_selfBoundary {D : Set (comparisonSpace σ₁ σ₂)}
    (hD : comparisonBoundary σ₁ σ₂ ⊆ closure D)
    (hmem : ∀ z ∈ D, comparisonSnd σ₁ σ₂ z ∈ σ₂.selfBoundary O₁) :
    comparisonBoundary σ₁ σ₂ ⊆ comparisonSnd σ₁ σ₂ ⁻¹' σ₂.selfBoundary O₁ :=
  hD.trans <| closure_minimal hmem <|
    isClosed_closure.preimage (comparisonSnd σ₁ σ₂).continuous

variable {σ₁ σ₂} in
/-- **Key boundary disjointness by density** (blueprint:
`lemma:nagata-comparison-boundary-density`, `lemma:nagata-key-boundary-disjointness`):
the combination of the two previous lemmas, which is the shape the improved-comparison
chain of the blueprint produces. -/
theorem keyDisjoint_of_dense_comparisonBoundary (h₂ : σ₂.Prepared O₁)
    {D : Set (comparisonSpace σ₁ σ₂)} (hD : comparisonBoundary σ₁ σ₂ ⊆ closure D)
    (hmem : ∀ z ∈ D, comparisonSnd σ₁ σ₂ z ∈ σ₂.selfBoundary O₁) :
    KeyDisjoint σ₁ σ₂ :=
  keyDisjoint_of_comparisonBoundary_subset h₂
    (comparisonBoundary_subset_preimage_selfBoundary hD hmem)

section Avoids

variable {σ₁ σ₂}
variable {A K : Type u} [CommRing A] [IsDomain A] [ValuationRing A] [Field K]
  [Algebra A K] [IsFractionRing A K]
  (η : Spec (CommRingCat.of K) ⟶ (O₁ ⊓ O₂ : U.Opens).toScheme)
  (g₁ : Spec (CommRingCat.of A) ⟶ σ₁.X.Z) (g₂ : Spec (CommRingCat.of A) ⟶ σ₂.X.Z)

/-- **One valuation extension avoids its forbidden boundary** (blueprint:
`lemma:nagata-valuation-pair-factors-comparison`,
`lemma:nagata-valuation-open-closed-point`,
`lemma:nagata-one-valuation-avoids-boundary`). -/
theorem KeyDisjoint.avoids (hkey : KeyDisjoint σ₁ σ₂)
    (hg₁ : Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ g₁ =
      η ≫ U.homOfLE inf_le_left ≫ (σ₁.υ ≫ σ₁.X.i))
    (hg₂ : Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ g₂ =
      η ≫ U.homOfLE inf_le_right ≫ (σ₂.υ ≫ σ₂.X.i))
    (hS : g₁ ≫ σ₁.X.g = g₂ ≫ σ₂.X.g) :
    Set.range g₁ ⊆ (σ₁.interiorLocus : Set σ₁.X.Z) ∨
      Set.range g₂ ⊆ (σ₂.interiorLocus : Set σ₂.X.Z) := by
  have := σ₁.isOpenImmersion_υ
  have := σ₂.isOpenImmersion_υ
  -- it suffices that one closed point avoids its forbidden boundary
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h₁, h₂⟩ := hcon
  have hclosed : ∀ {X₀ : Scheme.{u}} (g : Spec (CommRingCat.of A) ⟶ X₀)
      {F : Set X₀}, IsClosed F → ¬ Set.range g ⊆ Fᶜ →
      g (closedPoint (CommRingCat.of A)) ∈ F := by
    intro X₀ g F hF hne
    rw [Set.not_subset] at hne
    obtain ⟨-, ⟨a, rfl⟩, ha⟩ := hne
    rw [Set.mem_compl_iff, not_not] at ha
    exact ((specializes_closedPoint a).map g.continuous).mem_closed hF ha
  have hz₁ : g₁ (closedPoint (CommRingCat.of A)) ∈ σ₁.forbiddenBoundary :=
    hclosed g₁ isClosed_closure h₁
  have hz₂ : g₂ (closedPoint (CommRingCat.of A)) ∈ σ₂.forbiddenBoundary :=
    hclosed g₂ isClosed_closure h₂
  -- the pair of extensions as a morphism to `X₁ ×_S X₂`
  let ĝ : Spec (CommRingCat.of A) ⟶ pullback σ₁.X.g σ₂.X.g := pullback.lift g₁ g₂ hS
  have hĝ₁ : ĝ ≫ pullback.fst σ₁.X.g σ₂.X.g = g₁ := pullback.lift_fst _ _ _
  have hĝ₂ : ĝ ≫ pullback.snd σ₁.X.g σ₂.X.g = g₂ := pullback.lift_snd _ _ _
  -- the generic pair factors through `V₁ ×_U V₂`
  have hψ : (η ≫ U.homOfLE inf_le_left ≫ σ₁.υ) ≫ σ₁.ψ =
      (η ≫ U.homOfLE inf_le_right ≫ σ₂.υ) ≫ σ₂.ψ := by
    simp only [Category.assoc, σ₁.υ_ψ, σ₂.υ_ψ, Scheme.homOfLE_ι]
  let ηV : Spec (CommRingCat.of K) ⟶ pullback σ₁.ψ σ₂.ψ :=
    pullback.lift (η ≫ U.homOfLE inf_le_left ≫ σ₁.υ)
      (η ≫ U.homOfLE inf_le_right ≫ σ₂.υ) hψ
  have hηV₁ : ηV ≫ pullback.fst σ₁.ψ σ₂.ψ = η ≫ U.homOfLE inf_le_left ≫ σ₁.υ :=
    pullback.lift_fst _ _ _
  have hηV₂ : ηV ≫ pullback.snd σ₁.ψ σ₂.ψ = η ≫ U.homOfLE inf_le_right ≫ σ₂.υ :=
    pullback.lift_snd _ _ _
  have hcmp₁ : comparisonMap σ₁ σ₂ ≫ pullback.fst σ₁.X.g σ₂.X.g =
      pullback.fst σ₁.ψ σ₂.ψ ≫ σ₁.X.i := pullback.lift_fst _ _ _
  have hcmp₂ : comparisonMap σ₁ σ₂ ≫ pullback.snd σ₁.X.g σ₂.X.g =
      pullback.snd σ₁.ψ σ₂.ψ ≫ σ₂.X.i := pullback.lift_snd _ _ _
  -- the whole `Spec A` factors through the comparison space
  have hcomm : (ηV ≫ (comparisonMap σ₁ σ₂).toImage) ≫ (comparisonMap σ₁ σ₂).imageι =
      Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ ĝ := by
    rw [Category.assoc, Scheme.Hom.toImage_imageι]
    apply pullback.hom_ext
    · rw [Category.assoc, hcmp₁, reassoc_of% hηV₁, Category.assoc, hĝ₁, hg₁]
    · rw [Category.assoc, hcmp₂, reassoc_of% hηV₂, Category.assoc, hĝ₂, hg₂]
  obtain ⟨l, hl⟩ := IsClosedImmersion.exists_lift_of_isFractionRing
    (comparisonMap σ₁ σ₂).imageι ĝ (ηV ≫ (comparisonMap σ₁ σ₂).toImage) hcomm
  -- the closed point of the factorization violates the key disjointness
  have hl₁ : l ≫ comparisonFst σ₁ σ₂ = g₁ := by
    rw [comparisonFst, ← Category.assoc, hl, hĝ₁]
  have hl₂ : l ≫ comparisonSnd σ₁ σ₂ = g₂ := by
    rw [comparisonSnd, ← Category.assoc, hl, hĝ₂]
  have heq₁ : comparisonFst σ₁ σ₂ (l (closedPoint (CommRingCat.of A))) =
      g₁ (closedPoint (CommRingCat.of A)) :=
    calc comparisonFst σ₁ σ₂ (l (closedPoint (CommRingCat.of A)))
        = (l ≫ comparisonFst σ₁ σ₂) (closedPoint (CommRingCat.of A)) :=
          (Scheme.Hom.comp_apply _ _ _).symm
      _ = g₁ (closedPoint (CommRingCat.of A)) := by rw [hl₁]
  have heq₂ : comparisonSnd σ₁ σ₂ (l (closedPoint (CommRingCat.of A))) =
      g₂ (closedPoint (CommRingCat.of A)) :=
    calc comparisonSnd σ₁ σ₂ (l (closedPoint (CommRingCat.of A)))
        = (l ≫ comparisonSnd σ₁ σ₂) (closedPoint (CommRingCat.of A)) :=
          (Scheme.Hom.comp_apply _ _ _).symm
      _ = g₂ (closedPoint (CommRingCat.of A)) := by rw [hl₂]
  refine hkey (l (closedPoint (CommRingCat.of A))) ?_ ?_
  · rwa [heq₁]
  · rwa [heq₂]

end Avoids

section Improved

/-! ### The improved comparison space

After a `V₁`-admissible blow-up `π : X₁' ⟶ X₁` the comparison space of the improved pair
is a closed subscheme of the strict transform of the old comparison space along `π`: the
improved comparison morphism factors through that strict transform, and the
scheme-theoretic image of a morphism factoring through a closed subscheme is contained in
it. Consequently the improved first comparison projection inherits the injectivity of the
strict-transform projection, which is what the isomorphism near the boundary closure
(Stacks Project Tag 0F3W) supplies. -/

attribute [local instance] IsAdmissible.isProper_blowupMap IsAdmissible.isIso_blowupMap_restrict

variable [IsNoetherian S] (B : IsAdmissible σ₁.X.Z σ₁.X.i.opensRange)

/-- The transport of a side along an admissible blow-up embeds the (unchanged) proper
extension into the blow-up by the lift of the old embedding. -/
@[simp]
lemma admissibleBlowup_i :
    (σ₁.admissibleBlowup B).X.i = liftOfIsIsoRestrict B.I.blowupMap σ₁.X.i := rfl

/-- The base change along `X₁' ×_S X₂ ⟶ X₁ ×_S X₂` of the closed immersion of the
comparison space, exhibiting `X₁₂ ×_{X₁} X₁'` as a closed subscheme of `X₁' ×_S X₂`. -/
def blowupComparison :
    pullback (comparisonFst σ₁ σ₂) B.I.blowupMap ⟶ pullback (B.I.blowupMap ≫ σ₁.X.g) σ₂.X.g :=
  pullback.lift (pullback.snd (comparisonFst σ₁ σ₂) B.I.blowupMap)
    (pullback.fst (comparisonFst σ₁ σ₂) B.I.blowupMap ≫ comparisonSnd σ₁ σ₂)
    (by rw [← Category.assoc, ← pullback.condition, Category.assoc, Category.assoc,
      comparisonFst_s])

omit [IsNoetherian S] in
@[reassoc (attr := simp)]
lemma blowupComparison_fst :
    blowupComparison σ₁ σ₂ B ≫ pullback.fst (B.I.blowupMap ≫ σ₁.X.g) σ₂.X.g =
      pullback.snd (comparisonFst σ₁ σ₂) B.I.blowupMap :=
  pullback.lift_fst _ _ _

omit [IsNoetherian S] in
@[reassoc (attr := simp)]
lemma blowupComparison_snd :
    blowupComparison σ₁ σ₂ B ≫ pullback.snd (B.I.blowupMap ≫ σ₁.X.g) σ₂.X.g =
      pullback.fst (comparisonFst σ₁ σ₂) B.I.blowupMap ≫ comparisonSnd σ₁ σ₂ :=
  pullback.lift_snd _ _ _

omit [IsNoetherian S] in
lemma isPullback_blowupComparison :
    IsPullback (blowupComparison σ₁ σ₂ B)
      (pullback.fst (comparisonFst σ₁ σ₂) B.I.blowupMap)
      (partialSectionOpenι σ₁.X.g σ₂.X.g B.I.blowupMap) (comparisonMap σ₁ σ₂).imageι := by
  refine IsPullback.of_right ?_ ?_
    (isPullback_partialSectionOpenι σ₁.X.g σ₂.X.g B.I.blowupMap).flip
  · rw [blowupComparison_fst, ← comparisonFst_eq]
    exact (IsPullback.of_hasPullback _ _).flip
  · apply pullback.hom_ext
    · rw [Category.assoc, partialSectionOpenι_fst, blowupComparison_fst_assoc,
        Category.assoc, ← comparisonFst_eq]
      exact pullback.condition.symm
    · rw [Category.assoc, partialSectionOpenι_snd, blowupComparison_snd, Category.assoc,
        ← comparisonSnd_eq]

instance isClosedImmersion_blowupComparison :
    IsClosedImmersion (blowupComparison σ₁ σ₂ B) :=
  MorphismProperty.of_isPullback (isPullback_blowupComparison σ₁ σ₂ B).flip inferInstance

/-- The comparison morphism of the improved pair, viewed in `X₁₂ ×_{X₁} X₁'`. The
transport along the blow-up leaves the proper extension `ψ₁`, hence the fibre product
`V₁ ×_U V₂`, unchanged, so the first component is the old comparison morphism itself. -/
def improvedToPullback :
    pullback (σ₁.admissibleBlowup B).ψ σ₂.ψ ⟶ pullback (comparisonFst σ₁ σ₂) B.I.blowupMap :=
  pullback.lift (comparisonMap σ₁ σ₂).toImage
    (pullback.fst (σ₁.admissibleBlowup B).ψ σ₂.ψ ≫ (σ₁.admissibleBlowup B).X.i)
    (by
      rw [toImage_comparisonFst, Category.assoc, admissibleBlowup_i,
        liftOfIsIsoRestrict_comp]
      rfl)

@[reassoc (attr := simp)]
lemma improvedToPullback_fst :
    improvedToPullback σ₁ σ₂ B ≫ pullback.fst (comparisonFst σ₁ σ₂) B.I.blowupMap =
      (comparisonMap σ₁ σ₂).toImage :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma improvedToPullback_snd :
    improvedToPullback σ₁ σ₂ B ≫ pullback.snd (comparisonFst σ₁ σ₂) B.I.blowupMap =
      pullback.fst (σ₁.admissibleBlowup B).ψ σ₂.ψ ≫ (σ₁.admissibleBlowup B).X.i :=
  pullback.lift_snd _ _ _

/-- The factorization of the comparison morphism of the improved pair through the strict
transform of the old comparison space: the improved comparison lies over `V₁`, hence over
the preserved open of the blow-up. -/
def improvedToStrictTransform :
    pullback (σ₁.admissibleBlowup B).ψ σ₂.ψ ⟶
      strictTransform (comparisonFst σ₁ σ₂) B.I.blowupMap B.preservedOpen :=
  strictTransformOpenLift (comparisonFst σ₁ σ₂) B.I.blowupMap B.preservedOpen
      (improvedToPullback σ₁ σ₂ B)
      (by
        have h : improvedToPullback σ₁ σ₂ B ≫
            pullback.fst (comparisonFst σ₁ σ₂) B.I.blowupMap ≫ comparisonFst σ₁ σ₂ =
            pullback.fst σ₁.ψ σ₂.ψ ≫ σ₁.X.i := by
          rw [← Category.assoc, improvedToPullback_fst, toImage_comparisonFst]
        rw [h]
        rintro - ⟨w, rfl⟩
        have hmem : (pullback.fst σ₁.ψ σ₂.ψ ≫ σ₁.X.i) w ∈
            (σ₁.X.i.opensRange : Set σ₁.X.Z) := by
          rw [Scheme.Hom.comp_apply]
          exact ⟨_, rfl⟩
        exact B.le_preservedOpen hmem) ≫
    strictTransformFactor (comparisonFst σ₁ σ₂) B.I.blowupMap B.preservedOpen

@[reassoc]
lemma improvedToStrictTransform_strictTransformι :
    improvedToStrictTransform σ₁ σ₂ B ≫
        strictTransformι (comparisonFst σ₁ σ₂) B.I.blowupMap B.preservedOpen =
      improvedToPullback σ₁ σ₂ B := by
  rw [improvedToStrictTransform, Category.assoc, strictTransformFactor_ι,
    strictTransformOpenLift_ι]

/-- The closed immersion of the strict transform of the comparison space into
`X₁' ×_S X₂`. -/
def strictTransformComparisonι :
    strictTransform (comparisonFst σ₁ σ₂) B.I.blowupMap B.preservedOpen ⟶
      pullback (B.I.blowupMap ≫ σ₁.X.g) σ₂.X.g :=
  strictTransformι (comparisonFst σ₁ σ₂) B.I.blowupMap B.preservedOpen ≫
    blowupComparison σ₁ σ₂ B

instance isClosedImmersion_strictTransformComparisonι :
    IsClosedImmersion (strictTransformComparisonι σ₁ σ₂ B) := by
  rw [strictTransformComparisonι]
  infer_instance

omit [IsNoetherian S] in
lemma strictTransformComparisonι_fst :
    strictTransformComparisonι σ₁ σ₂ B ≫ pullback.fst (B.I.blowupMap ≫ σ₁.X.g) σ₂.X.g =
      strictTransformMap (comparisonFst σ₁ σ₂) B.I.blowupMap B.preservedOpen := by
  rw [strictTransformComparisonι, Category.assoc, blowupComparison_fst]
  rfl

lemma improvedToStrictTransform_ι :
    improvedToStrictTransform σ₁ σ₂ B ≫ strictTransformComparisonι σ₁ σ₂ B =
      comparisonMap (σ₁.admissibleBlowup B) σ₂ := by
  rw [strictTransformComparisonι, improvedToStrictTransform_strictTransformι_assoc]
  apply pullback.hom_ext
  · rw [Category.assoc, blowupComparison_fst, improvedToPullback_snd]
    exact (comparisonMap_fst (σ₁.admissibleBlowup B) σ₂).symm
  · rw [Category.assoc, blowupComparison_snd, ← Category.assoc, improvedToPullback_fst,
      toImage_comparisonSnd]
    exact (comparisonMap_snd (σ₁.admissibleBlowup B) σ₂).symm

/-- **Injectivity of the improved first comparison projection near the boundary**: on an
open of the blown-up model over which the strict transform of the old first projection is
an isomorphism, the first projection of the improved comparison space is injective. This
is where Stacks Project Tag 0F3W enters the comparison layer. -/
theorem injOn_comparisonFst_admissibleBlowup {N' : B.I.blowup.Opens}
    (hiso : IsIso (strictTransformMap (comparisonFst σ₁ σ₂) B.I.blowupMap
      B.preservedOpen ∣_ N')) :
    Set.InjOn ⇑(comparisonFst (σ₁.admissibleBlowup B) σ₂)
      (⇑(comparisonFst (σ₁.admissibleBlowup B) σ₂) ⁻¹' (N' : Set B.I.blowup)) := by
  -- the improved comparison space is a closed subscheme of the strict transform
  have hsub : Set.range ⇑(comparisonMap (σ₁.admissibleBlowup B) σ₂) ⊆
      Set.range ⇑(strictTransformComparisonι σ₁ σ₂ B) := by
    rw [← improvedToStrictTransform_ι σ₁ σ₂ B]
    rintro - ⟨w, rfl⟩
    exact ⟨improvedToStrictTransform σ₁ σ₂ B w, (Scheme.Hom.comp_apply _ _ _).symm⟩
  have hrange : Set.range ⇑(comparisonMap (σ₁.admissibleBlowup B) σ₂).imageι ⊆
      Set.range ⇑(strictTransformComparisonι σ₁ σ₂ B) := by
    have h : Set.range ⇑(comparisonMap (σ₁.admissibleBlowup B) σ₂).imageι =
        closure (Set.range ⇑(comparisonMap (σ₁.admissibleBlowup B) σ₂)) := by
      rw [← Scheme.Hom.support_ker, ← Scheme.IdealSheafData.range_subschemeι]
    rw [h]
    exact closure_minimal hsub
      (strictTransformComparisonι σ₁ σ₂ B).isClosedEmbedding.isClosed_range
  -- the strict-transform projection is injective over `N'`
  have hstinj : ∀ a b, strictTransformMap (comparisonFst σ₁ σ₂) B.I.blowupMap
      B.preservedOpen a = strictTransformMap (comparisonFst σ₁ σ₂) B.I.blowupMap
      B.preservedOpen b → strictTransformMap (comparisonFst σ₁ σ₂) B.I.blowupMap
      B.preservedOpen a ∈ (N' : Set B.I.blowup) → a = b := by
    intro a b hab ha
    have hb : strictTransformMap (comparisonFst σ₁ σ₂) B.I.blowupMap B.preservedOpen b ∈
        (N' : Set B.I.blowup) := hab ▸ ha
    have ha' : a ∈ Set.range ⇑(strictTransformMap (comparisonFst σ₁ σ₂) B.I.blowupMap
        B.preservedOpen ⁻¹ᵁ N').ι := by
      rw [Scheme.Opens.range_ι]
      exact ha
    have hb' : b ∈ Set.range ⇑(strictTransformMap (comparisonFst σ₁ σ₂) B.I.blowupMap
        B.preservedOpen ⁻¹ᵁ N').ι := by
      rw [Scheme.Opens.range_ι]
      exact hb
    obtain ⟨a', rfl⟩ := ha'
    obtain ⟨b', rfl⟩ := hb'
    have hres : (strictTransformMap (comparisonFst σ₁ σ₂) B.I.blowupMap
        B.preservedOpen ∣_ N') a' = (strictTransformMap (comparisonFst σ₁ σ₂) B.I.blowupMap
        B.preservedOpen ∣_ N') b' := by
      apply N'.ι.isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, morphismRestrict_ι,
        Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hab]
    rw [(Scheme.homeoOfIso (asIso (strictTransformMap (comparisonFst σ₁ σ₂) B.I.blowupMap
      B.preservedOpen ∣_ N'))).injective hres]
  -- the comparison projections agree with the strict-transform projection
  have hstw : ∀ (z : comparisonSpace (σ₁.admissibleBlowup B) σ₂)
      (w : strictTransform (comparisonFst σ₁ σ₂) B.I.blowupMap B.preservedOpen),
      strictTransformComparisonι σ₁ σ₂ B w =
        (comparisonMap (σ₁.admissibleBlowup B) σ₂).imageι z →
      strictTransformMap (comparisonFst σ₁ σ₂) B.I.blowupMap B.preservedOpen w =
        comparisonFst (σ₁.admissibleBlowup B) σ₂ z := by
    intro z w hzw
    rw [← strictTransformComparisonι_fst σ₁ σ₂ B, Scheme.Hom.comp_apply, hzw,
      comparisonFst_eq, Scheme.Hom.comp_apply]
    rfl
  intro z₁ hz₁ z₂ hz₂ heq
  obtain ⟨w₁, hw₁⟩ := hrange (Set.mem_range_self z₁)
  obtain ⟨w₂, hw₂⟩ := hrange (Set.mem_range_self z₂)
  have h₁ := hstw z₁ w₁ hw₁
  have h₂ := hstw z₂ w₂ hw₂
  have hww : w₁ = w₂ := hstinj w₁ w₂ (by rw [h₁, h₂, heq]) (by rw [h₁]; exact hz₁)
  apply (comparisonMap (σ₁.admissibleBlowup B) σ₂).imageι.isClosedEmbedding.injective
  rw [← hw₁, ← hw₂, hww]

end Improved

end CompactifiedProperExtension

open CompactifiedProperExtension in
/-- **The improved comparison** (Stacks Project Tag 0F3W; blueprint:
`lemma:nagata-comparison-restrict-proper-open`,
`def:nagata-two-open-improved-comparison`,
`lemma:nagata-comparison-isIso-near-boundary`,
`lemma:nagata-comparison-boundary-density`).

This is the geometric core of the comparison layer. The forbidden boundary locus
`Z₁,₂ = ψ₁⁻¹(U ∖ O₁)` is closed in `V₁` and lies in the open `CompactifiedProperExtension.isoOpen`
over which the proper first comparison projection is an isomorphism, because
`U ∖ O₁ ⊆ O₂` and `ψ₂` is an isomorphism over `O₂`. So the isomorphism-near-closure
blow-up (Tag 0F3W) applies and produces a `V₁`-admissible blow-up `π : X₁' ⟶ X₁` and
an open `N'` of `X₁'` containing the closure of `π⁻¹(Z₁,₂)` over which the strict
transform of the first projection is an isomorphism.

The improved comparison space is a closed subscheme of that strict transform
(`injOn_comparisonFst_admissibleBlowup`), so its first projection `p₁` is injective
over `N'`; it is also proper, hence closed, and surjective over `π⁻¹(Z₁,₂)`. An
injective closed map is a homeomorphism onto its image, so `p₁⁻¹` of the closure of
`π⁻¹(Z₁,₂)` — which is the comparison boundary of the improved pair — is contained in
the closure of `p₁⁻¹(π⁻¹(Z₁,₂))`. On the latter the second projection lands in the
self boundary of the second side, because there the comparison space is the fibre
product `V₁' ×_U V₂` and both projections have the same image in `U`; the density
criterion `comparisonBoundary_subset_preimage_selfBoundary` then concludes.

The blow-up shape of the conclusion is the one the surrounding API was built for:
`CompactifiedProperExtension.admissibleBlowup` and
`CompactifiedProperExtension.Prepared.admissibleBlowup` both cite
`def:nagata-two-open-improved-comparison`, and preparedness of the improved first side
is exactly what the latter supplies. No preparedness of the two sides is assumed. -/
theorem exists_admissibleBlowup_comparisonBoundary_subset_selfBoundary [IsNoetherian S]
    {u : U ⟶ S} [IsSeparated u] [LocallyOfFiniteType u] [QuasiCompact u]
    {O₁ O₂ : U.Opens} (σ₁ : CompactifiedProperExtension u O₁)
    (σ₂ : CompactifiedProperExtension u O₂) (hcov : O₁ ⊔ O₂ = ⊤) :
    ∃ B : IsAdmissible σ₁.X.Z σ₁.X.i.opensRange,
      comparisonBoundary (σ₁.admissibleBlowup B) σ₂ ⊆
        comparisonSnd (σ₁.admissibleBlowup B) σ₂ ⁻¹' σ₂.selfBoundary O₁ := by
  have hXN := σ₁.isNoetherian_Z
  have hqs : QuasiSeparatedSpace σ₁.X.Z :=
    ⟨fun _ _ _ _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have := isProper_comparisonFst σ₁ σ₂
  -- the complement of `O₁` is contained in `O₂`, where the second extension is an iso
  have hOsub : ((O₁ : Set U)ᶜ) ⊆ (O₂ : Set U) := by
    intro x hx
    have huniv : ((O₁ : Set U) ∪ (O₂ : Set U)) = Set.univ := by
      have h := congrArg (fun W : U.Opens ↦ (W : Set U)) hcov
      simpa using h
    rcases Set.eq_univ_iff_forall.mp huniv x with h | h
    · exact absurd h hx
    · exact h
  -- the boundary locus `Z₁,₂`, a closed subset of `V₁` inside the isomorphism open
  have hTU : ⇑σ₁.X.i '' (⇑σ₁.ψ ⁻¹' ((O₁ : Set U)ᶜ)) ⊆ (σ₁.X.i.opensRange : Set σ₁.X.Z) := by
    rintro - ⟨v, -, rfl⟩
    exact ⟨v, rfl⟩
  have hTcl : IsClosed (⇑(σ₁.X.i.opensRange).ι ⁻¹'
      (⇑σ₁.X.i '' (⇑σ₁.ψ ⁻¹' ((O₁ : Set U)ᶜ)))) := by
    have hA : IsClosed (⇑σ₁.ψ ⁻¹' ((O₁ : Set U)ᶜ)) :=
      O₁.isOpen.isClosed_compl.preimage σ₁.ψ.continuous
    have he : ⇑σ₁.X.i = ⇑(σ₁.X.i.opensRange).ι ∘ ⇑σ₁.X.i.isoOpensRange.hom := by
      conv_lhs => rw [← Scheme.Hom.isoOpensRange_hom_ι σ₁.X.i]
      rfl
    rw [he, Set.image_comp,
      Set.preimage_image_eq _ (σ₁.X.i.opensRange).ι.isOpenEmbedding.injective]
    exact ((Scheme.homeoOfIso σ₁.X.i.isoOpensRange).isClosedMap _ hA)
  have hTN : ⇑σ₁.X.i '' (⇑σ₁.ψ ⁻¹' ((O₁ : Set U)ᶜ)) ⊆ (isoOpen σ₁ σ₂ : Set σ₁.X.Z) := by
    rw [isoOpen_eq_image]
    exact Set.image_mono (Set.preimage_mono hOsub)
  -- Stacks Project Tag 0F3W applied to the proper first comparison projection
  obtain ⟨B, N', hcl, hiso⟩ :=
    exists_admissibleBlowup_isIso_strictTransformMap_near_closure
      (TopologicalSpace.NoetherianSpace.isCompact _) (comparisonFst σ₁ σ₂) hTU hTcl hTN
      (isIso_comparisonFst_restrict_isoOpen σ₁ σ₂)
  refine ⟨B, ?_⟩
  have hproper : IsProper (comparisonFst (σ₁.admissibleBlowup B) σ₂) :=
    isProper_comparisonFst _ _
  -- the transported boundary locus
  have hpre : ⇑B.I.blowupMap ⁻¹' (⇑σ₁.X.i '' (⇑σ₁.ψ ⁻¹' ((O₁ : Set U)ᶜ))) =
      ⇑(σ₁.admissibleBlowup B).X.i ''
        (⇑(σ₁.admissibleBlowup B).ψ ⁻¹' ((O₁ : Set U)ᶜ)) :=
    (σ₁.admissibleBlowup_image_preimage B ((O₁ : Set U)ᶜ)).symm
  set D : Set (comparisonSpace (σ₁.admissibleBlowup B) σ₂) :=
    ⇑(comparisonFst (σ₁.admissibleBlowup B) σ₂) ⁻¹'
      (⇑B.I.blowupMap ⁻¹' (⇑σ₁.X.i '' (⇑σ₁.ψ ⁻¹' ((O₁ : Set U)ᶜ)))) with hDdef
  -- (1) the second projection of `D` lands in the self boundary of the second side
  have hmem : ∀ z ∈ D, comparisonSnd (σ₁.admissibleBlowup B) σ₂ z ∈ σ₂.selfBoundary O₁ := by
    intro z hz
    have hz' : comparisonFst (σ₁.admissibleBlowup B) σ₂ z ∈
        ⇑(σ₁.admissibleBlowup B).X.i ''
          (⇑(σ₁.admissibleBlowup B).ψ ⁻¹' ((O₁ : Set U)ᶜ)) := by
      rw [← hpre]
      exact hz
    have hzV : z ∈ ⇑(comparisonFst (σ₁.admissibleBlowup B) σ₂) ⁻¹'
        ((σ₁.admissibleBlowup B).X.i.opensRange : Set (σ₁.admissibleBlowup B).X.Z) := by
      obtain ⟨v, -, hv⟩ := hz'
      rw [Set.mem_preimage, ← hv]
      exact ⟨v, rfl⟩
    rw [← range_toImage_comparisonMap] at hzV
    obtain ⟨w, rfl⟩ := hzV
    obtain ⟨v, hv, hvw⟩ := hz'
    have hveq : v = pullback.fst (σ₁.admissibleBlowup B).ψ σ₂.ψ w := by
      apply (σ₁.admissibleBlowup B).X.i.isOpenEmbedding.injective
      rw [hvw, comparisonFst_toImage_apply]
    rw [comparisonSnd_toImage_apply]
    refine subset_closure ⟨pullback.snd (σ₁.admissibleBlowup B).ψ σ₂.ψ w, ?_, rfl⟩
    rw [Set.mem_preimage, ← ψ_pullback_fst_apply, ← hveq]
    exact hv
  -- (2) the comparison boundary of the improved pair is in the closure of `D`
  have hDcl : comparisonBoundary (σ₁.admissibleBlowup B) σ₂ ⊆ closure D := by
    have hsurjT : ⇑B.I.blowupMap ⁻¹' (⇑σ₁.X.i '' (⇑σ₁.ψ ⁻¹' ((O₁ : Set U)ᶜ))) ⊆
        Set.range ⇑(comparisonFst (σ₁.admissibleBlowup B) σ₂) := by
      rw [hpre]
      rintro - ⟨v, hv, rfl⟩
      obtain ⟨w, hw⟩ :=
        preimage_subset_range_pullback_fst (σ₁.admissibleBlowup B) σ₂ (hOsub hv)
      exact ⟨(comparisonMap (σ₁.admissibleBlowup B) σ₂).toImage w, by
        rw [comparisonFst_toImage_apply, hw]⟩
    have himg : closure (⇑B.I.blowupMap ⁻¹' (⇑σ₁.X.i '' (⇑σ₁.ψ ⁻¹' ((O₁ : Set U)ᶜ)))) ⊆
        ⇑(comparisonFst (σ₁.admissibleBlowup B) σ₂) '' closure D := by
      refine closure_minimal ?_
        ((comparisonFst (σ₁.admissibleBlowup B) σ₂).isClosedMap _ isClosed_closure)
      intro x hx
      obtain ⟨z', hz'⟩ := hsurjT hx
      exact ⟨z', subset_closure (by rw [hDdef, Set.mem_preimage, hz']; exact hx), hz'⟩
    intro z hz
    have hzcl : comparisonFst (σ₁.admissibleBlowup B) σ₂ z ∈
        closure (⇑B.I.blowupMap ⁻¹' (⇑σ₁.X.i '' (⇑σ₁.ψ ⁻¹' ((O₁ : Set U)ᶜ)))) := by
      have hz2 : comparisonFst (σ₁.admissibleBlowup B) σ₂ z ∈
          (σ₁.admissibleBlowup B).forbiddenBoundary := hz
      rwa [σ₁.admissibleBlowup_forbiddenBoundary B] at hz2
    obtain ⟨e, he, hee⟩ := himg hzcl
    have hzN : comparisonFst (σ₁.admissibleBlowup B) σ₂ z ∈ (N' : Set B.I.blowup) :=
      hcl hzcl
    have hze : z = e := injOn_comparisonFst_admissibleBlowup σ₁ σ₂ B hiso
      (by rw [Set.mem_preimage]; exact hzN)
      (by rw [Set.mem_preimage, hee]; exact hzN) hee.symm
    rwa [hze]
  exact comparisonBoundary_subset_preimage_selfBoundary hDcl hmem

open CompactifiedProperExtension in
/-- **Existence of a prepared, key-disjoint pair of sides** (blueprint:
`lemma:nagata-comparison-restrict-proper-open`,
`def:nagata-two-open-improved-comparison`,
`lemma:nagata-comparison-isIso-near-boundary`,
`lemma:nagata-comparison-boundary-density`,
`lemma:nagata-key-boundary-disjointness`).

The first side is improved by the isomorphism-near-closure blow-up (Stacks Project
Tag 0F3W) of the first comparison projection at the forbidden boundary locus.

The proof consumes the modification layer only through
`exists_admissibleBlowup_comparisonBoundary_subset_selfBoundary`, and therefore
depends on `sorryAx` only through Stacks Project Tag 081S; see the module
docstring. -/
theorem exists_prepared_keyDisjoint_compactifiedProperExtension [IsNoetherian S] (u : U ⟶ S)
    [IsSeparated u] [LocallyOfFiniteType u] [QuasiCompact u] (O₁ O₂ : U.Opens)
    (hcov : O₁ ⊔ O₂ = ⊤) [HasCompactification (O₁.ι ≫ u)]
    [HasCompactification (O₂.ι ≫ u)] :
    ∃ (σ₁ : CompactifiedProperExtension u O₁) (σ₂ : CompactifiedProperExtension u O₂),
      σ₁.Prepared O₂ ∧ σ₂.Prepared O₁ ∧ KeyDisjoint σ₁ σ₂ := by
  obtain ⟨σ₁, h₁⟩ := exists_prepared_compactifiedProperExtension u O₁ O₂ hcov
  obtain ⟨σ₂, h₂⟩ :=
    exists_prepared_compactifiedProperExtension u O₂ O₁ (by rw [sup_comm]; exact hcov)
  obtain ⟨B, hB⟩ :=
    exists_admissibleBlowup_comparisonBoundary_subset_selfBoundary σ₁ σ₂ hcov
  exact ⟨σ₁.admissibleBlowup B, σ₂, CompactifiedProperExtension.Prepared.admissibleBlowup B h₁,
    h₂, keyDisjoint_of_comparisonBoundary_subset h₂ hB⟩

/-- The bundled output of the comparison layer of the two-open compactification
theorem: two prepared sides satisfying the key boundary disjointness. This is the
input of the final assembly. -/
structure TwoOpenPreparation (u : U ⟶ S) (O₁ O₂ : U.Opens) where
  /-- The prepared side over the first open. -/
  side₁ : CompactifiedProperExtension u O₁
  /-- The prepared side over the second open. -/
  side₂ : CompactifiedProperExtension u O₂
  /-- The first side is prepared. -/
  prepared₁ : side₁.Prepared O₂
  /-- The second side is prepared. -/
  prepared₂ : side₂.Prepared O₁
  /-- The two sides satisfy the key boundary disjointness. -/
  keyDisjoint : CompactifiedProperExtension.KeyDisjoint side₁ side₂

/-- Existence of the comparison-layer data of the two-open compactification
theorem. -/
theorem nonempty_twoOpenPreparation [IsNoetherian S] (u : U ⟶ S) [IsSeparated u]
    [LocallyOfFiniteType u] [QuasiCompact u] (O₁ O₂ : U.Opens) (hcov : O₁ ⊔ O₂ = ⊤)
    [HasCompactification (O₁.ι ≫ u)] [HasCompactification (O₂.ι ≫ u)] :
    Nonempty (TwoOpenPreparation u O₁ O₂) := by
  obtain ⟨σ₁, σ₂, h₁, h₂, hkey⟩ :=
    exists_prepared_keyDisjoint_compactifiedProperExtension u O₁ O₂ hcov
  exact ⟨⟨σ₁, σ₂, h₁, h₂, hkey⟩⟩

end AlgebraicGeometry
