/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Compactification.CommonModification
public import WeilConjectures.Compactification.TwoOpenComparison
public import WeilConjectures.Compactification.ValuativeCriterion
public import WeilConjectures.Mathlib.AlgebraicGeometry.Gluing

/-!

# The two-open compactification theorem

This file assembles the **two-open compactification theorem** (Stacks Project
Tag 0F40; blueprint chapter "Nagata compactification", section "The two-open
compactification theorem", proof order items 43–48): over a Noetherian base `S`, a
separated finite-type morphism `u : U ⟶ S` is compactifiable as soon as `U` is covered
by two compactifiable opens with dense intersection
(`AlgebraicGeometry.HasCompactification.of_two_open_cover`).

The intermediate schemes of the construction are built from a prepared side
`σ : TwoOpenSide u O`:

- `AlgebraicGeometry.TwoOpenSide.intermediate`: the glued scheme
  `Wᵢ = U ⊔_{O} Xᵢ°` obtained by gluing `U` and the complement `Xᵢ°` of the forbidden
  boundary along the embedded copy of `O` (blueprint:
  `def:nagata-two-open-intermediate-schemes`; proof order item 43), with its two
  charts `intermediateU`, `intermediateInterior` and structure morphism
  `intermediateHom`;
- `AlgebraicGeometry.TwoOpenSide.isClosedImmersion_intermediateGraph`: the overlap
  `O ⟶ U ×_S Xᵢ°` is a closed immersion — its range is the preimage of the closed
  range of the proper graph `V ⟶ U ×_S X` (blueprint:
  `lemma:nagata-proper-extension-graph-closed` through
  `lemma:nagata-intermediate-overlap-closed`; the constructibility detour of the
  blueprint is bypassed by the exact description `range υ = ψ⁻¹(O)`);
- `AlgebraicGeometry.TwoOpenSide.isSeparated_intermediateHom`: `Wᵢ ⟶ S` is separated
  (Stacks Project Tag 0F3U via `IsSeparated.pushout_desc`; blueprint:
  `lemma:nagata-intermediate-separated`);
- `AlgebraicGeometry.TwoOpenSide.dense_range_intermediateU`: the copy of `U` is dense
  in `Wᵢ` (blueprint: part of `lemma:nagata-two-open-density-transport`).

The final theorem `HasCompactification.of_two_open_cover` then applies the common
modification (Stacks Project Tag 0F3X, `nonempty_commonModification`; blueprint
`def:nagata-two-open-final-modification`, `lemma:nagata-two-open-final-modification`;
item 45) to `W₁`, `W₂`, transports density through the finite modification diagram
(blueprint: `lemma:nagata-two-open-density-transport`, `lemma:nagata-final-density`;
items 46–47), proves unique valuative lifting from the dense source `O₁ ∩ O₂` using
the proper valuative criterion of the sides and the boundary-avoidance property of the
comparison layer (blueprint: `lemma:nagata-proper-separated-valuation-extension`,
`lemma:nagata-two-open-valuative-lifting`; item 44), and concludes properness by the
dense-source valuative criterion (Stacks Project Tag 0894,
`UniversallyClosed.of_valuativeCriterion_of_isDominant`; blueprint:
`lemma:nagata-two-open-candidate-proper`, `thm:nagata-two-open`; item 48).

-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits IsLocalRing

namespace AlgebraicGeometry

variable {U S : Scheme.{u}}

namespace TwoOpenSide

variable {u : U ⟶ S} {O : U.Opens} (σ : TwoOpenSide u O)

section Intermediate

lemma interiorEmb_comm : O.ι ≫ u = σ.interiorEmb ≫ σ.interior.ι ≫ σ.s := by
  rw [σ.interiorEmb_ι_assoc, σ.embX_s]

/-- The **intermediate scheme** `Wᵢ = U ⊔_O Xᵢ°` of a side: the gluing of `U` and the
complement of the forbidden boundary along the embedded copy of `O`.
(Blueprint: `def:nagata-two-open-intermediate-schemes`; proof order item 43.) -/
def intermediate : Scheme.{u} := pushout O.ι σ.interiorEmb

/-- The chart `U ⟶ Wᵢ` of the intermediate scheme. -/
def intermediateU : U ⟶ σ.intermediate := pushout.inl O.ι σ.interiorEmb

/-- The chart `Xᵢ° ⟶ Wᵢ` of the intermediate scheme. -/
def intermediateInterior : σ.interior.toScheme ⟶ σ.intermediate :=
  pushout.inr O.ι σ.interiorEmb

instance : IsOpenImmersion σ.intermediateU :=
  inferInstanceAs (IsOpenImmersion (pushout.inl O.ι σ.interiorEmb))

instance : IsOpenImmersion σ.intermediateInterior :=
  inferInstanceAs (IsOpenImmersion (pushout.inr O.ι σ.interiorEmb))

@[reassoc]
lemma intermediate_condition :
    O.ι ≫ σ.intermediateU = σ.interiorEmb ≫ σ.intermediateInterior :=
  pushout.condition

/-- The structure morphism `Wᵢ ⟶ S` of the intermediate scheme. -/
def intermediateHom : σ.intermediate ⟶ S :=
  pushout.desc u (σ.interior.ι ≫ σ.s) σ.interiorEmb_comm

@[reassoc (attr := simp)]
lemma intermediateU_hom : σ.intermediateU ≫ σ.intermediateHom = u :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
lemma intermediateInterior_hom :
    σ.intermediateInterior ≫ σ.intermediateHom = σ.interior.ι ≫ σ.s :=
  pushout.inr_desc _ _ _

lemma range_intermediateU_union :
    Set.range σ.intermediateU ∪ Set.range σ.intermediateInterior = Set.univ :=
  range_pushout_inl_union_range_pushout_inr O.ι σ.interiorEmb

/-- **The copy of `U` is dense in the intermediate scheme**: the second chart is the
complement of the forbidden boundary, in which the embedded copy of `O` is dense.
(Blueprint: part of `lemma:nagata-two-open-density-transport`.) -/
theorem dense_range_intermediateU : Dense (Set.range σ.intermediateU) := by
  rw [dense_iff_inter_open]
  rintro W₀ hW₀ ⟨w₀, hw₀⟩
  have hw₀cov : w₀ ∈ Set.range σ.intermediateU ∪ Set.range σ.intermediateInterior := by
    rw [σ.range_intermediateU_union]
    trivial
  obtain ⟨a, rfl⟩ | ⟨p, rfl⟩ := hw₀cov
  · exact ⟨σ.intermediateU a, hw₀, a, rfl⟩
  · -- transport the open to `X` and use density of the copy of `O`
    have hopen : IsOpen (σ.interior.ι '' (σ.intermediateInterior ⁻¹' W₀)) :=
      σ.interior.ι.isOpenEmbedding.isOpenMap _
        (hW₀.preimage σ.intermediateInterior.continuous)
    obtain ⟨d, hd, hdD⟩ := dense_iff_inter_open.mp σ.dense_range_embX _ hopen
      ⟨σ.interior.ι p, ⟨p, hw₀, rfl⟩⟩
    obtain ⟨q, hq, hqd⟩ := hd
    obtain ⟨o, rfl⟩ := hdD
    have hqEmb : q = σ.interiorEmb o := by
      apply σ.interior.ι.isOpenEmbedding.injective
      rw [hqd]
      exact congrArg (fun m ↦ m) (by rw [← σ.interiorEmb_ι]; exact Scheme.Hom.comp_apply _ _ _)
    refine ⟨σ.intermediateInterior q, ?_, ?_⟩
    · exact hq
    · refine ⟨O.ι o, ?_⟩
      rw [hqEmb, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
        σ.intermediate_condition]

section Graph

/-- The proper graph `γ : V ⟶ U ×_S X` of the proper extension `ψ`.
(Blueprint: `lemma:nagata-proper-extension-graph-closed`.) -/
def graph : σ.V.toScheme ⟶ pullback u σ.s := pullback.lift σ.ψ σ.V.ι σ.ψ_u

@[reassoc (attr := simp)]
lemma graph_fst : σ.graph ≫ pullback.fst u σ.s = σ.ψ := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma graph_snd : σ.graph ≫ pullback.snd u σ.s = σ.V.ι := pullback.lift_snd _ _ _

/-- The graph of the proper extension is proper; in particular its range is closed.
(Blueprint: `lemma:nagata-proper-extension-graph-closed`.) -/
theorem isProper_graph : IsProper σ.graph := by
  have := σ.isProper_ψ
  have := σ.isProper_s
  have : IsProper (σ.graph ≫ pullback.fst u σ.s) := by
    rw [σ.graph_fst]
    exact σ.isProper_ψ
  exact IsProper.of_comp σ.graph (pullback.fst u σ.s)

/-- The open immersion `U ×_S Xᵢ° ⟶ U ×_S X` induced by the inclusion of the
complement of the forbidden boundary. -/
def intermediateOpenι : pullback u (σ.interior.ι ≫ σ.s) ⟶ pullback u σ.s :=
  pullback.map u (σ.interior.ι ≫ σ.s) u σ.s (𝟙 U) σ.interior.ι (𝟙 S) (by simp) (by simp)

instance : IsOpenImmersion σ.intermediateOpenι :=
  MorphismProperty.pullbackMap (P := @IsOpenImmersion) inferInstance inferInstance
    (by simp) rfl

@[reassoc (attr := simp)]
lemma intermediateOpenι_fst :
    σ.intermediateOpenι ≫ pullback.fst u σ.s = pullback.fst u (σ.interior.ι ≫ σ.s) ≫ 𝟙 U :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma intermediateOpenι_snd :
    σ.intermediateOpenι ≫ pullback.snd u σ.s =
      pullback.snd u (σ.interior.ι ≫ σ.s) ≫ σ.interior.ι :=
  pullback.lift_snd _ _ _

/-- The overlap map `O ⟶ U ×_S Xᵢ°` of the two charts of the intermediate scheme. -/
def intermediateGraph : O.toScheme ⟶ pullback u (σ.interior.ι ≫ σ.s) :=
  pullback.lift O.ι σ.interiorEmb σ.interiorEmb_comm

@[reassoc (attr := simp)]
lemma intermediateGraph_fst :
    σ.intermediateGraph ≫ pullback.fst u (σ.interior.ι ≫ σ.s) = O.ι :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma intermediateGraph_snd :
    σ.intermediateGraph ≫ pullback.snd u (σ.interior.ι ≫ σ.s) = σ.interiorEmb :=
  pullback.lift_snd _ _ _

lemma intermediateGraph_openι :
    σ.intermediateGraph ≫ σ.intermediateOpenι = σ.υ ≫ σ.graph := by
  apply pullback.hom_ext
  · rw [Category.assoc, σ.intermediateOpenι_fst, σ.intermediateGraph_fst_assoc,
      Category.comp_id, Category.assoc, σ.graph_fst, σ.υ_ψ]
  · rw [Category.assoc, σ.intermediateOpenι_snd, σ.intermediateGraph_snd_assoc,
      σ.interiorEmb_ι, Category.assoc, σ.graph_snd]
    rfl

/-- **The overlap of the two charts of the intermediate scheme is a closed immersion**
(blueprint: `lemma:nagata-intermediate-overlap-constructible` through
`lemma:nagata-intermediate-overlap-closed`).

The range of the overlap map is the preimage of the closed range of the proper graph
`V ⟶ U ×_S X`, because over the complement of the forbidden boundary the graph passes
through the embedded copy of `O` exactly over `O` (`TwoOpenSide.range_υ`). -/
theorem isClosedImmersion_intermediateGraph :
    IsClosedImmersion σ.intermediateGraph := by
  have := σ.isOpenImmersion_υ
  have hprop := σ.isProper_graph
  -- the overlap map is an immersion since its first projection is an open immersion
  have : IsImmersion (σ.intermediateGraph ≫ pullback.fst u (σ.interior.ι ≫ σ.s)) := by
    rw [σ.intermediateGraph_fst]
    infer_instance
  have : IsImmersion σ.intermediateGraph :=
    IsImmersion.of_comp σ.intermediateGraph (pullback.fst u (σ.interior.ι ≫ σ.s))
  refine IsClosedImmersion.of_isPreimmersion _ ?_
  -- the range is the preimage of the closed range of the proper graph
  · have hkey : Set.range σ.intermediateGraph =
        σ.intermediateOpenι ⁻¹' (Set.range σ.graph) := by
      apply subset_antisymm
      · rintro - ⟨o, rfl⟩
        refine Set.mem_preimage.mpr ⟨σ.υ o, ?_⟩
        rw [← Scheme.Hom.comp_apply, ← σ.intermediateGraph_openι, Scheme.Hom.comp_apply]
      · intro t ht
        obtain ⟨v, hv⟩ := Set.mem_preimage.mp ht
        -- the second component of the graph point lies in the interior
        have hvV : σ.V.ι v ∈ (σ.interior : Set σ.X) := by
          have h1 : σ.V.ι v = (σ.graph ≫ pullback.snd u σ.s) v := by
            rw [σ.graph_snd]
          have h2 : (σ.graph ≫ pullback.snd u σ.s) v =
              pullback.snd u σ.s (σ.intermediateOpenι t) := by
            rw [Scheme.Hom.comp_apply, hv]
          have h3 : pullback.snd u σ.s (σ.intermediateOpenι t) =
              σ.interior.ι (pullback.snd u (σ.interior.ι ≫ σ.s) t) := by
            calc pullback.snd u σ.s (σ.intermediateOpenι t)
                = (σ.intermediateOpenι ≫ pullback.snd u σ.s) t :=
                  (Scheme.Hom.comp_apply _ _ _).symm
              _ = (pullback.snd u (σ.interior.ι ≫ σ.s) ≫ σ.interior.ι) t := by
                  rw [σ.intermediateOpenι_snd]
              _ = σ.interior.ι (pullback.snd u (σ.interior.ι ≫ σ.s) t) :=
                  Scheme.Hom.comp_apply _ _ _
          rw [h1, h2, h3, ← Scheme.Opens.range_ι]
          exact ⟨_, rfl⟩
        -- hence the graph point passes through the embedded copy of `O`
        have hvO : v ∈ Set.range σ.υ := by
          rw [σ.range_υ]
          by_contra hvO
          have hvZ : σ.V.ι v ∈ σ.V.ι '' (σ.ψ ⁻¹' ((O : Set U)ᶜ)) :=
            ⟨v, fun h ↦ hvO h, rfl⟩
          exact hvV (subset_closure hvZ)
        obtain ⟨o, rfl⟩ := hvO
        refine ⟨o, ?_⟩
        apply σ.intermediateOpenι.isOpenEmbedding.injective
        rw [← Scheme.Hom.comp_apply, σ.intermediateGraph_openι, Scheme.Hom.comp_apply, hv]
    rw [hkey]
    exact (σ.graph.isClosedMap.isClosed_range).preimage σ.intermediateOpenι.continuous

end Graph

section Structure

/-- **Separatedness of the intermediate scheme** (Stacks Project Tag 0F3U; blueprint:
`lemma:nagata-intermediate-separated`): the two charts of `Wᵢ ⟶ S` are separated and
their overlap is a closed immersion. -/
theorem isSeparated_intermediateHom [IsSeparated u] : IsSeparated σ.intermediateHom := by
  have := σ.isProper_s
  have : IsSeparated (σ.interior.ι ≫ σ.s) := inferInstance
  exact IsSeparated.pushout_desc O.ι σ.interiorEmb σ.interiorEmb_comm
    σ.isClosedImmersion_intermediateGraph

/-- The intermediate scheme is of finite type over the base (blueprint:
`lemma:nagata-intermediate-separated`, finite-type part). -/
theorem locallyOfFiniteType_intermediateHom [LocallyOfFiniteType u] :
    LocallyOfFiniteType σ.intermediateHom := by
  have := σ.isProper_s
  exact IsZariskiLocalAtSource.pushout_desc O.ι σ.interiorEmb σ.interiorEmb_comm
    inferInstance inferInstance

/-- The intermediate scheme of a side over a Noetherian base is quasi-compact. -/
theorem compactSpace_intermediate [IsNoetherian S] [QuasiCompact u] :
    CompactSpace σ.intermediate := by
  have : IsNoetherian σ.X := σ.isNoetherian_X
  have : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace u
  have : CompactSpace σ.interior.toScheme :=
    isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact _)
  exact inferInstanceAs (CompactSpace ↑(pushout O.ι σ.interiorEmb))

/-- The intermediate scheme of a side over a Noetherian base is Noetherian. -/
theorem isNoetherian_intermediate [IsNoetherian S] [LocallyOfFiniteType u]
    [QuasiCompact u] : IsNoetherian σ.intermediate := by
  have : IsLocallyNoetherian σ.intermediate := by
    have := σ.locallyOfFiniteType_intermediateHom
    exact LocallyOfFiniteType.isLocallyNoetherian σ.intermediateHom
  have := σ.compactSpace_intermediate
  exact ⟨⟩

end Structure

end Intermediate

end TwoOpenSide

open TwoOpenSide in
/-- **The two-open compactification theorem** (Stacks Project Tag 0F40; blueprint:
`def:nagata-two-open-final-modification` through `thm:nagata-two-open`; proof order
items 43–48).

The compactification is the common modification `W` (Stacks Project Tag 0F3X) of the
two intermediate schemes `Wᵢ = U ⊔_{Oᵢ} Xᵢ°`; the intersection `O₁ ∩ O₂` is dense in
`W` because density transports through the finite modification diagram, every
valuative square through it lifts uniquely — extend the generic point to the proper
sides, pass to the side avoiding its forbidden boundary, and lift along the proper
admissible blow-up — and the dense-source valuative criterion (Stacks Project
Tag 0894) then proves that `W ⟶ S` is universally closed, hence proper. -/
theorem HasCompactification.of_two_open_cover [IsNoetherian S] (u : U ⟶ S)
    [IsSeparated u] [LocallyOfFiniteType u] [QuasiCompact u] (O₁ O₂ : U.Opens)
    (hcov : O₁ ⊔ O₂ = ⊤) (hdense : Dense ((O₁ ⊓ O₂ : U.Opens) : Set U))
    [HasCompactification (O₁.ι ≫ u)] [HasCompactification (O₂.ι ≫ u)] :
    HasCompactification u := by
  -- basic instances
  have : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian u
  have : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace u
  have : IsNoetherian U := ⟨⟩
  -- the comparison layer: prepared sides with the key boundary disjointness
  obtain ⟨P⟩ := nonempty_twoOpenPreparation u O₁ O₂ hcov
  have := P.side₁.isProper_s
  have := P.side₂.isProper_s
  -- the two intermediate schemes are separated, of finite type and Noetherian
  have : IsSeparated P.side₁.intermediateHom := P.side₁.isSeparated_intermediateHom
  have : IsSeparated P.side₂.intermediateHom := P.side₂.isSeparated_intermediateHom
  have : LocallyOfFiniteType P.side₁.intermediateHom :=
    P.side₁.locallyOfFiniteType_intermediateHom
  have : LocallyOfFiniteType P.side₂.intermediateHom :=
    P.side₂.locallyOfFiniteType_intermediateHom
  have : IsNoetherian P.side₁.intermediate := P.side₁.isNoetherian_intermediate
  have : IsNoetherian P.side₂.intermediate := P.side₂.isNoetherian_intermediate
  -- the common modification of the two intermediate schemes (Stacks 0F3X)
  obtain ⟨cm⟩ := nonempty_commonModification P.side₁.intermediateHom
    P.side₂.intermediateHom P.side₁.intermediateU P.side₂.intermediateU
    (by rw [P.side₁.intermediateU_hom, P.side₂.intermediateU_hom])
  -- the open immersion of `U` into the glued scheme
  have hu₁OI : IsOpenImmersion cm.u₁ :=
    isOpenImmersion_of_comp_of_isIso_restrict cm.u₁ cm.B₁.I.blowupMap
      P.side₁.intermediateU cm.u₁_blowupMap cm.B₁.isIso_blowupMap_restrict
  have hu₂OI : IsOpenImmersion cm.u₂ :=
    isOpenImmersion_of_comp_of_isIso_restrict cm.u₂ cm.B₂.I.blowupMap
      P.side₂.intermediateU cm.u₂_blowupMap cm.B₂.isIso_blowupMap_restrict
  set jW : U ⟶ cm.W := cm.u₁ ≫ cm.k₁ with hjW_def
  have : IsOpenImmersion jW := inferInstance
  have hjWu : jW ≫ cm.w = u := by
    rw [hjW_def, Category.assoc, cm.k₁_w, ← Category.assoc, cm.u₁_blowupMap,
      P.side₁.intermediateU_hom]
  -- the dense quasi-compact source `O₁ ∩ O₂ ⟶ W`
  set h : (O₁ ⊓ O₂ : U.Opens).toScheme ⟶ cm.W := (O₁ ⊓ O₂ : U.Opens).ι ≫ jW with hh_def
  have hhw : h ≫ cm.w = (O₁ ⊓ O₂ : U.Opens).ι ≫ u := by
    rw [hh_def, Category.assoc, hjWu]
  have : CompactSpace (O₁ ⊓ O₂ : U.Opens).toScheme :=
    isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact _)
  have : IsNoetherian (O₁ ⊓ O₂ : U.Opens).toScheme := ⟨⟩
  have : QuasiCompact h := inferInstance
  have : QuasiSeparated h := inferInstance
  -- density transport (blueprint: items 46–47): the copies of `U` are dense in the
  -- two modified charts, and `O₁ ∩ O₂` is dense in `U`
  have hdense₁ : Dense (Set.range cm.u₁) := by
    rw [range_eq_preimage_of_comp_of_isIso_restrict cm.u₁ cm.B₁.I.blowupMap
      P.side₁.intermediateU cm.u₁_blowupMap cm.B₁.isIso_blowupMap_restrict]
    exact cm.B₁.dense_preimage_blowupMap P.side₁.dense_range_intermediateU
  have hdense₂ : Dense (Set.range cm.u₂) := by
    rw [range_eq_preimage_of_comp_of_isIso_restrict cm.u₂ cm.B₂.I.blowupMap
      P.side₂.intermediateU cm.u₂_blowupMap cm.B₂.isIso_blowupMap_restrict]
    exact cm.B₂.dense_preimage_blowupMap P.side₂.dense_range_intermediateU
  have hdom : IsDominant h := by
    constructor
    rw [DenseRange, dense_iff_inter_open]
    rintro W₀ hW₀ ⟨w₀, hw₀⟩
    have chartCase : ∀ {W' : Scheme.{u}} (k : W' ⟶ cm.W) (uu : U ⟶ W'),
        IsOpenImmersion k → Dense (Set.range uu) → uu ≫ k = jW →
        w₀ ∈ Set.range k → (W₀ ∩ Set.range h).Nonempty := by
      intro W' k uu hkOI hdu hglue hw₀k
      have := hkOI
      obtain ⟨b₀, rfl⟩ := hw₀k
      obtain ⟨b, hbW₀, y, rfl⟩ := dense_iff_inter_open.mp hdu (k ⁻¹' W₀)
        (hW₀.preimage k.continuous) ⟨b₀, hw₀⟩
      obtain ⟨d, hdW, hdO⟩ := dense_iff_inter_open.mp hdense (uu ⁻¹' (k ⁻¹' W₀))
        ((hW₀.preimage k.continuous).preimage uu.continuous) ⟨y, hbW₀⟩
      obtain ⟨p, rfl⟩ : d ∈ Set.range (O₁ ⊓ O₂ : U.Opens).ι := by
        rwa [Scheme.Opens.range_ι]
      refine ⟨h p, ?_, p, rfl⟩
      have heq : h p = k (uu ((O₁ ⊓ O₂ : U.Opens).ι p)) :=
        calc h p = jW ((O₁ ⊓ O₂ : U.Opens).ι p) := Scheme.Hom.comp_apply _ _ _
          _ = (uu ≫ k) ((O₁ ⊓ O₂ : U.Opens).ι p) := by rw [hglue]
          _ = k (uu ((O₁ ⊓ O₂ : U.Opens).ι p)) := Scheme.Hom.comp_apply _ _ _
      rwa [heq]
    have hw₀cov : w₀ ∈ Set.range cm.k₁ ∪ Set.range cm.k₂ := by
      rw [cm.cover]
      trivial
    obtain hw₀k | hw₀k := hw₀cov
    · exact chartCase cm.k₁ cm.u₁ inferInstance hdense₁ hjW_def.symm hw₀k
    · exact chartCase cm.k₂ cm.u₂ inferInstance hdense₂
        (cm.u_glue.symm.trans hjW_def.symm) hw₀k
  -- the dense-source valuative criterion (Stacks 0894): `W ⟶ S` is universally closed
  have huc : UniversallyClosed cm.w := by
    refine UniversallyClosed.of_valuativeCriterion_of_isDominant cm.w h
      (ValuativeCriterion.RelativeTo.of_existsUnique ?_)
    rintro ⟨R, K, i₁, i₂, ⟨wsq⟩⟩ ηU hηU
    let : Field (CommRingCat.of K) := ‹_›
    replace hηU : ηU ≫ h = i₁ := hηU
    -- extend the generic point to the two proper ambient models
    have hexist : ∀ {O : U.Opens} (σ : TwoOpenSide u O) (hle : O₁ ⊓ O₂ ≤ O),
        ∃ g : Spec (CommRingCat.of R) ⟶ σ.X,
          Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ g =
            ηU ≫ U.homOfLE hle ≫ σ.embX ∧ g ≫ σ.s = i₂ := by
      intro O σ hle
      have := σ.isProper_s
      have hcomm : (ηU ≫ U.homOfLE hle ≫ σ.embX) ≫ σ.s =
          Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ i₂ := by
        have h1 : (ηU ≫ U.homOfLE hle ≫ σ.embX) ≫ σ.s =
            ηU ≫ (O₁ ⊓ O₂ : U.Opens).ι ≫ u := by
          simp only [Category.assoc, TwoOpenSide.embX_s, Scheme.homOfLE_ι_assoc]
        rw [h1, ← hhw, ← Category.assoc, hηU, wsq]
      have hE : ValuativeCriterion.Existence σ.s := by
        have huc' : (ValuativeCriterion.Existence ⊓ @QuasiCompact) σ.s := by
          rw [← UniversallyClosed.eq_valuativeCriterion]
          infer_instance
        exact huc'.1
      obtain ⟨⟨l, hl₁, hl₂⟩⟩ := (hE
        { R := R
          K := K
          i₁ := ηU ≫ U.homOfLE hle ≫ σ.embX
          i₂ := i₂
          commSq := ⟨hcomm⟩ }).exists_lift
      exact ⟨l, hl₁, hl₂⟩
    obtain ⟨g₁, hg₁, hg₁s⟩ := hexist P.side₁ inf_le_left
    obtain ⟨g₂, hg₂, hg₂s⟩ := hexist P.side₂ inf_le_right
    -- one extension avoids its forbidden boundary
    have havoid := P.keyDisjoint.avoids ηU g₁ g₂ hg₁ hg₂ (by rw [hg₁s, hg₂s])
    -- the avoiding extension lifts to the glued scheme through the corresponding
    -- intermediate model and its admissible blow-up
    have branch : ∀ {O : U.Opens} (σ : TwoOpenSide u O) (hle : O₁ ⊓ O₂ ≤ O)
        (B : IsAdmissible σ.intermediate σ.intermediateU.opensRange)
        (k : B.I.blowup ⟶ cm.W) (uu : U ⟶ B.I.blowup),
        uu ≫ B.I.blowupMap = σ.intermediateU →
        k ≫ cm.w = B.I.blowupMap ≫ σ.intermediateHom →
        uu ≫ k = jW →
        ∀ g : Spec (CommRingCat.of R) ⟶ σ.X,
        Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ g =
          ηU ≫ U.homOfLE hle ≫ σ.embX →
        g ≫ σ.s = i₂ → Set.range g ⊆ (σ.interior : Set σ.X) →
        ∃ l : Spec (CommRingCat.of R) ⟶ cm.W,
          Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ l = i₁ ∧ l ≫ cm.w = i₂ := by
      intro O σ hle B k uu huu hkw hglue g hg hgs hrange
      have := σ.isProper_s
      have := σ.isOpenImmersion_υ
      -- corestrict to the complement of the forbidden boundary
      let g₀ : Spec (CommRingCat.of R) ⟶ σ.interior.toScheme :=
        IsOpenImmersion.lift σ.interior.ι g (by rwa [Scheme.Opens.range_ι])
      have hg₀ : g₀ ≫ σ.interior.ι = g := IsOpenImmersion.lift_fac _ _ _
      -- the resulting morphism to the intermediate scheme
      set m : Spec (CommRingCat.of R) ⟶ σ.intermediate :=
        g₀ ≫ σ.intermediateInterior with hm_def
      have hmw : m ≫ σ.intermediateHom = i₂ := by
        rw [hm_def, Category.assoc, σ.intermediateInterior_hom, ← Category.assoc, hg₀,
          hgs]
      -- the generic point factors through the embedded copy of `O`
      have hgen : Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ g₀ =
          ηU ≫ U.homOfLE hle ≫ σ.interiorEmb := by
        rw [← cancel_mono σ.interior.ι, Category.assoc, hg₀, hg]
        simp only [Category.assoc, TwoOpenSide.interiorEmb_ι]
      -- the valuative square along the proper admissible blow-up
      have hsqB : (ηU ≫ (O₁ ⊓ O₂ : U.Opens).ι ≫ uu) ≫ B.I.blowupMap =
          Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ m := by
        have h1 : (ηU ≫ (O₁ ⊓ O₂ : U.Opens).ι ≫ uu) ≫ B.I.blowupMap =
            ηU ≫ (O₁ ⊓ O₂ : U.Opens).ι ≫ σ.intermediateU := by
          simp only [Category.assoc, huu]
        have h2 : Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ m =
            ηU ≫ U.homOfLE hle ≫ σ.interiorEmb ≫ σ.intermediateInterior := by
          rw [hm_def, ← Category.assoc, hgen]
          simp only [Category.assoc]
        rw [h1, h2, ← σ.intermediate_condition]
        simp only [Scheme.homOfLE_ι_assoc]
      have := B.isProper_blowupMap
      have hEB : ValuativeCriterion.Existence B.I.blowupMap := by
        have huc' : (ValuativeCriterion.Existence ⊓ @QuasiCompact) B.I.blowupMap := by
          rw [← UniversallyClosed.eq_valuativeCriterion]
          infer_instance
        exact huc'.1
      obtain ⟨⟨n, hn₁, hn₂⟩⟩ := (hEB
        { R := R
          K := K
          i₁ := ηU ≫ (O₁ ⊓ O₂ : U.Opens).ι ≫ uu
          i₂ := m
          commSq := ⟨hsqB⟩ }).exists_lift
      refine ⟨n ≫ k, ?_, ?_⟩
      · rw [← Category.assoc, hn₁]
        simp only [Category.assoc]
        rw [hglue, ← hh_def, hηU]
      · rw [Category.assoc, hkw, ← Category.assoc, hn₂, hmw]
    have hlift : ∃ l : Spec (CommRingCat.of R) ⟶ cm.W,
        Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ l = i₁ ∧ l ≫ cm.w = i₂ := by
      obtain h₁ | h₂ := havoid
      · exact branch P.side₁ inf_le_left cm.B₁ cm.k₁ cm.u₁ cm.u₁_blowupMap cm.k₁_w
          hjW_def.symm g₁ hg₁ hg₁s h₁
      · exact branch P.side₂ inf_le_right cm.B₂ cm.k₂ cm.u₂ cm.u₂_blowupMap cm.k₂_w
          (cm.u_glue.symm.trans hjW_def.symm) g₂ hg₂ hg₂s h₂
    -- uniqueness from separatedness of the glued scheme
    obtain ⟨l, hl₁, hl₂⟩ := hlift
    refine ⟨l, ⟨hl₁, hl₂⟩, ?_⟩
    intro l' hl'
    have huniq := IsSeparated.valuativeCriterion (f := cm.w)
      { R := R
        K := K
        i₁ := i₁
        i₂ := i₂
        commSq := ⟨wsq⟩ }
    exact congrArg CommSq.LiftStruct.l
      (@Subsingleton.elim _ huniq ⟨l', hl'.1, hl'.2⟩ ⟨l, hl₁, hl₂⟩)
  -- `W ⟶ S` is proper, and `U ⟶ W` is a quasi-compact open immersion
  have : IsProper cm.w := ⟨⟩
  exact ⟨⟨{ Z := cm.W
            g := cm.w
            i := jW
            comm := hjWu.symm
            isProper := inferInstance
            isOpenImmersion := inferInstance }⟩⟩

end AlgebraicGeometry
