/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.AlgebraicGeometry.NoetherianApproximation.RelativeGluingDescent

/-!
# The valid stage of the relative gluing datum

Let `M` be chart models over the stage `D_i` of a finite relative affine presentation of a
scheme `X` of finite presentation over `lim Dⱼ`, and let `d` be a relative gluing datum at a
stage `j ≥ i` whose base change to the limit is compatible with the charts `ℓₐ : Lₐ ⟶ X` (for
instance the raw datum `AlgebraicGeometry.RelativeAffinePresentation.ChartModels.rawDatum`).
Then each of the finitely many gluing axioms (overlap opens matching, identities, cocycles)
holds for `d` at the limit, hence holds at every stage past a selected equality stage
(`lemma-nagata-qc-open-eq-eventually`, `lemma-nagata-morphism-eq-eventually`, in the forms of
`AlgebraicGeometry.exists_forall_map_preimage_le`,
`AlgebraicGeometry.exists_forall_resLE_preimage_le` and
`AlgebraicGeometry.exists_forall_resLE_comp_eq`). A common lower bound of these stages is the
valid stage `λ_rel`.

The axioms are dealt with in two rounds: the open conditions first, since the cocycle
condition only makes sense once the overlap maps are known to map the triple overlaps into the
overlaps.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.RelativeAffinePresentation.ChartModels

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} {c : Cone D} (hc : IsLimit c)
  [IsCofiltered I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
  {X : Scheme.{u}} {g : X ⟶ c.pt} {R : RelativeAffinePresentation c g} (M : R.ChartModels)

lemma stage_w {j j' : Over M.stage} (f : j' ⟶ j) :
    D.map f.left ≫ D.map j.hom = D.map j'.hom := by
  rw [← D.map_comp, Over.w f]

/-- The transport of a datum at the stage `j` to a later stage `j'`. -/
noncomputable abbrev stageTransport {j j' : Over M.stage} (f : j' ⟶ j)
    (d : RelativeGluingDatum M.p (D.map j.hom)) : RelativeGluingDatum M.p (D.map j'.hom) :=
  d.transport (D.map f.left) (M.stage_w f)

lemma chartMap_stage_eq {j j' : Over M.stage} (f : j' ⟶ j) (a : R.J) :
    RelativeGluingDatum.chartMap M.p (D.map f.left) (M.stage_w f) a =
      (baseChangeDiagram D (M.p a)).map f :=
  rfl

/-- Compatibility of the limit transport is inherited by later stages. -/
lemma isCompatible_limitTransport_stageTransport {j j' : Over M.stage} (f : j' ⟶ j)
    {d : RelativeGluingDatum M.p (D.map j.hom)}
    (hd : RelativeGluingDatum.IsCompatible M.ℓ (M.limitTransport d)) :
    RelativeGluingDatum.IsCompatible M.ℓ (M.limitTransport (M.stageTransport f d)) :=
  RelativeGluingDatum.IsCompatible.of_isTransport
    (RelativeGluingDatum.isTransport_transport _ _ d)
    ((RelativeGluingDatum.isTransport_transport _ _ _).trans
      (RelativeGluingDatum.isTransport_transport _ _ d))
    (c.w f.left).symm hd

variable [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]

lemma isCompact_stageTransport_V {j j' : Over M.stage} (f : j' ⟶ j)
    {d : RelativeGluingDatum M.p (D.map j.hom)}
    (hd : ∀ a b, IsCompact (d.V a b : Set ↥(pullback (M.p a) (D.map j.hom)))) (a b : R.J) :
    IsCompact ((M.stageTransport f d).V a b : Set ↥(pullback (M.p a) (D.map j'.hom))) :=
  QuasiCompact.isCompact_preimage ((baseChangeDiagram D (M.p a)).map f) (d.V a b).2 (hd a b)

lemma isCompact_ι_preimage {j : Over M.stage} (a : R.J)
    {V W : (pullback (M.p a) (D.map j.hom)).Opens}
    (hV : IsCompact (V : Set ↥(pullback (M.p a) (D.map j.hom))))
    (hW : IsCompact (W : Set ↥(pullback (M.p a) (D.map j.hom)))) :
    IsCompact (V.ι ⁻¹ᵁ W : Set V.toScheme) := by
  have e : (V.ι ⁻¹ᵁ W : Set V.toScheme) = V.ι ⁻¹' ((V : Set _) ∩ W) := by
    ext x
    simp [Scheme.Opens.ι_apply, x.2]
  rw [e, V.ι.isOpenEmbedding.isInducing.isCompact_preimage_iff (by
    rw [Scheme.Opens.range_ι]
    exact Set.inter_subset_left)]
  exact QuasiSeparatedSpace.inter_isCompact _ _ V.2 hV W.2 hW

/-- First round: the open gluing axioms hold past some stage. -/
theorem exists_isOpenValid {j : Over M.stage} (d : RelativeGluingDatum M.p (D.map j.hom))
    (hd : RelativeGluingDatum.IsCompatible M.ℓ (M.limitTransport d))
    (hVc : ∀ a b, IsCompact (d.V a b : Set ↥(pullback (M.p a) (D.map j.hom)))) :
    ∃ k₀ : Over j, ∀ (k : Over j) (_ : k ⟶ k₀), (M.stageTransport k.hom d).IsOpenValid := by
  have hov := hd.isValid.isOpenValid
  have hT := RelativeGluingDatum.isTransport_transport (c.π.app j.left) (c.w j.hom) d
  choose kself hkself using fun a ↦ exists_forall_map_preimage_le
    (isLimitBaseChangeCone D c (M.p a) hc) (l := j) (U := ⊤) (V := d.V a a)
    (by simpa using isCompact_univ) (by
      have := hov.V_self a
      rw [hT.V_eq] at this
      rw [Scheme.Hom.preimage_top]
      exact this.ge)
  choose kcoc hkcoc using fun x : R.J × R.J × R.J ↦ exists_forall_resLE_preimage_le
    (isLimitBaseChangeCone D c (M.p x.1) hc) (d.V x.1 x.2.1)
    ((d.V x.1 x.2.1).ι ⁻¹ᵁ d.V x.1 x.2.2) (d.map x.1 x.2.1 ⁻¹ᵁ d.V x.2.1 x.2.2)
    (M.isCompact_ι_preimage x.1 (hVc _ _) (hVc _ _)) (by
      have := hov.le_preimage x.1 x.2.1 x.2.2
      rw [hT.preimage_ι_eq, hT.preimage_map_eq] at this
      exact this)
  obtain ⟨k₀, hk₀⟩ := IsCofiltered.exists_forall_nonempty_hom (Sum.elim kself kcoc)
  refine ⟨k₀, fun k f ↦ ?_⟩
  have hT' := RelativeGluingDatum.isTransport_transport (D.map k.hom.left) (M.stage_w k.hom) d
  refine ⟨fun a ↦ ?_, fun a b c ↦ ?_⟩
  · refine le_antisymm le_top ?_
    have := hkself a k (f ≫ (hk₀ (Sum.inl a)).some)
    rw [Scheme.Hom.preimage_top] at this
    exact this
  · rw [hT'.preimage_ι_eq, hT'.preimage_map_eq]
    exact hkcoc (a, b, c) k (f ≫ (hk₀ (Sum.inr (a, b, c))).some)

/-- Second round: if the open gluing axioms hold, all gluing axioms hold past some stage. -/
theorem exists_isValid {j : Over M.stage} (d : RelativeGluingDatum M.p (D.map j.hom))
    (hd : RelativeGluingDatum.IsCompatible M.ℓ (M.limitTransport d)) (hov : d.IsOpenValid)
    (hVc : ∀ a b, IsCompact (d.V a b : Set ↥(pullback (M.p a) (D.map j.hom)))) :
    ∃ k₀ : Over j, ∀ (k : Over j) (_ : k ⟶ k₀), (M.stageTransport k.hom d).IsValid := by
  have hv := hd.isValid
  have hT := RelativeGluingDatum.isTransport_transport (c.π.app j.left) (c.w j.hom) d
  choose kself hkself using fun a ↦ exists_forall_resLE_comp_eq
    (isLimitBaseChangeCone D c (M.p a) hc) (baseChangeDiagramStructure D (M.p a)) (hVc a a)
    (M.p a) (d.ψ a a) ((d.V a a).ι ≫ pullback.fst _ _) (by rw [d.ψ_comp]; rfl) (by simp) (by
      calc _ = (M.limitTransport d).ψ a a := rfl
        _ = _ := hv.ψ_self a
        _ = _ := by rw [Scheme.Hom.resLE_comp_ι_assoc, baseChangeCone_π_app_fst])
  choose kcoc hkcoc using fun x : R.J × R.J × R.J ↦ exists_forall_resLE_comp_eq
    (isLimitBaseChangeCone D c (M.p x.1) hc) (baseChangeDiagramStructure D (M.p x.1))
    (QuasiSeparatedSpace.inter_isCompact _ _ (d.V _ _).2 (hVc _ _) (d.V _ _).2 (hVc _ _))
    (M.p x.2.2) (RelativeGluingDatum.cocycleMap hov x.1 x.2.1 x.2.2 ≫ d.ψ x.2.1 x.2.2)
    ((pullback (M.p x.1) (D.map j.hom)).homOfLE inf_le_right ≫ d.ψ x.1 x.2.2)
    (by
      rw [Category.assoc, d.ψ_comp, RelativeGluingDatum.cocycleMap_ι_assoc, Category.assoc,
        RelativeGluingDatum.map_fst_assoc, d.ψ_comp, Scheme.homOfLE_ι_assoc]
      rfl)
    (by
      rw [Category.assoc, d.ψ_comp, Scheme.homOfLE_ι_assoc]
      rfl)
    (by
      rw [hT.resLE_cocycle_left hov hv.isOpenValid _ _ _ _ _ le_rfl,
        hT.resLE_cocycle_right _ _ _ _ _ le_rfl, hv.cocycle])
  obtain ⟨k₀, hk₀⟩ := IsCofiltered.exists_forall_nonempty_hom (Sum.elim kself kcoc)
  refine ⟨k₀, fun k f ↦ ?_⟩
  have hT' := RelativeGluingDatum.isTransport_transport (D.map k.hom.left) (M.stage_w k.hom) d
  have hov' := hT'.isOpenValid hov
  refine ⟨hov', fun a ↦ ?_, fun a b c ↦ ?_⟩
  · have := hkself a k (f ≫ (hk₀ (Sum.inl a)).some)
    rw [Scheme.Hom.resLE_comp_ι_assoc] at this
    refine this.trans ?_
    rw [← chartMap_stage_eq, RelativeGluingDatum.chartMap_fst]
  · have := hkcoc (a, b, c) k (f ≫ (hk₀ (Sum.inr (a, b, c))).some)
    have e := congrArg ((pullback (M.p a) (D.map k.left.hom)).homOfLE
      (le_rfl : (M.stageTransport k.hom d).V a b ⊓ (M.stageTransport k.hom d).V a c ≤ _) ≫ ·)
      this
    simp only [Scheme.homOfLE_comp_resLE_assoc] at e
    rw [← chartMap_stage_eq, hT'.resLE_cocycle_left hov hov' _ _ _ _ _ le_rfl,
      hT'.resLE_cocycle_right _ _ _ _ _ le_rfl, Scheme.homOfLE_rfl, Category.id_comp,
      Category.id_comp] at e
    exact e

variable [QuasiSeparatedSpace X]

lemma isCompact_rawDatum_V (a b : R.J) :
    IsCompact ((M.rawDatum hc).V a b : Set ↥(pullback (M.p a) (D.map (M.rawStage hc).hom))) :=
  QuasiCompact.isCompact_preimage _ (Scheme.Hom.preimage _ _).2
    (QuasiCompact.isCompact_preimage _ (M.overlapOpen hc a b).2 (M.isCompact_overlapOpen hc a b))

/-- The selected stage past `λ_raw` at which the open gluing axioms hold. -/
noncomputable def openStage : Over (M.rawStage hc) :=
  (M.exists_isOpenValid hc (M.rawDatum hc) (M.isCompatible_rawDatum hc)
    (M.isCompact_rawDatum_V hc)).choose

/-- The raw datum transported to `M.openStage`. -/
noncomputable def openDatum : RelativeGluingDatum M.p (D.map (M.openStage hc).left.hom) :=
  M.stageTransport (M.openStage hc).hom (M.rawDatum hc)

lemma isOpenValid_openDatum : (M.openDatum hc).IsOpenValid :=
  (M.exists_isOpenValid hc (M.rawDatum hc) (M.isCompatible_rawDatum hc)
    (M.isCompact_rawDatum_V hc)).choose_spec _ (𝟙 _)

lemma isCompatible_openDatum :
    RelativeGluingDatum.IsCompatible M.ℓ (M.limitTransport (M.openDatum hc)) :=
  M.isCompatible_limitTransport_stageTransport _ (M.isCompatible_rawDatum hc)

lemma isCompact_openDatum_V (a b : R.J) :
    IsCompact ((M.openDatum hc).V a b :
      Set ↥(pullback (M.p a) (D.map (M.openStage hc).left.hom))) :=
  M.isCompact_stageTransport_V _ (M.isCompact_rawDatum_V hc) a b

/-- (Implementation) The selected stage past `M.openStage` at which all gluing axioms hold. -/
noncomputable def validStage : Over (M.openStage hc).left :=
  (M.exists_isValid hc (M.openDatum hc) (M.isCompatible_openDatum hc)
    (M.isOpenValid_openDatum hc) (M.isCompact_openDatum_V hc)).choose

/-- Blueprint `def-nagata-relative-gluing-valid-stage`: Cocycle-valid stage for the relative
datum.

The stage `λ_rel`, lying past `λ_raw` (via `relStageToRawStage`),
obtained as a selected common bound of the equality stages of the finitely many required
equalities of overlap opens (first round, `M.openStage`) and of the identity and cocycle
equalities (second round). -/
noncomputable def relStage : Over M.stage := (M.validStage hc).left

/-- The transition `λ_rel ⟶ λ_raw`. -/
noncomputable def relStageToRawStage : M.relStage hc ⟶ M.rawStage hc :=
  (M.validStage hc).hom ≫ (M.openStage hc).hom

/-- Part of blueprint `def-nagata-relative-gluing-valid-stage`: the raw datum transported to
the stage `λ_rel`, the datum `R_{X,λ_rel}`. -/
noncomputable def validDatum : RelativeGluingDatum M.p (D.map (M.relStage hc).hom) :=
  M.stageTransport (M.validStage hc).hom (M.openDatum hc)

/-- Blueprint `lemma-nagata-relative-gluing-axioms-eventually`: The relative gluing axioms hold
at the selected stage. In `R_{X,λ_rel}` the overlap opens match, the overlap maps are inverse
(`AlgebraicGeometry.RelativeGluingDatum.toOpensGlueData`) and all triple-overlap cocycle
identities hold. -/
theorem isValid_validDatum : (M.validDatum hc).IsValid :=
  (M.exists_isValid hc (M.openDatum hc) (M.isCompatible_openDatum hc)
    (M.isOpenValid_openDatum hc) (M.isCompact_openDatum_V hc)).choose_spec _ (𝟙 _)

/-- The base change of `R_{X,λ_rel}` to the limit is the overlap datum of `X`. -/
theorem isCompatible_validDatum :
    RelativeGluingDatum.IsCompatible M.ℓ (M.limitTransport (M.validDatum hc)) :=
  M.isCompatible_limitTransport_stageTransport _ (M.isCompatible_openDatum hc)

lemma isCompact_validDatum_V (a b : R.J) :
    IsCompact ((M.validDatum hc).V a b :
      Set ↥(pullback (M.p a) (D.map (M.relStage hc).hom))) :=
  M.isCompact_stageTransport_V _ (M.isCompact_openDatum_V hc) a b

end AlgebraicGeometry.RelativeAffinePresentation.ChartModels
