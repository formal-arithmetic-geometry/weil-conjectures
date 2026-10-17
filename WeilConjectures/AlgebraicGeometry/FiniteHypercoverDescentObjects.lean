/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteHypercoverDescentStage

/-!
# Descent of truncated finite split étale hypercovers to a stage

Starting from `AlgebraicGeometry.HypercoverStageData`, we show that the splitting cofans become
coproducts at a later stage, construct the matching objects at the stage as finite limits of
qcqs étale schemes, show that the matching maps become surjective at a later stage, and assemble
a truncated finite split étale hypercover at that stage whose base change is the given one.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} {c : Cone D} {r : ℕ}
  {U : TruncatedFiniteSplitEtaleHypercover c.pt r}

/-- The index type of the summands of the splitting in degree `Δ`. -/
abbrev SplitIndex {r : ℕ} (Δ : (SimplexCategory.Truncated r)ᵒᵖ) : Type :=
  Σ m : Fin (r + 1), {α : Δ.unop.obj ⟶ SimplexCategory.mk m.val // Epi α}

namespace HypercoverStageData

variable {i : I} (S : HypercoverStageData D c U i)

/-- The legs of the splitting cofan at the stage. -/
def leg (Δ : (SimplexCategory.Truncated r)ᵒᵖ) (x : SplitIndex Δ) : S.N x.1 ⟶ S.G.obj Δ :=
  S.ι x.1 ≫ S.G.map (SimplexCategory.Truncated.Hom.tr x.2.val Δ.unop.property
    (Nat.le_of_lt_succ x.1.isLt)).op

lemma leg_e (Δ : (SimplexCategory.Truncated r)ᵒᵖ) (x : SplitIndex Δ) :
    (Over.pullback (c.π.app i)).map (S.leg Δ x) ≫ S.e.hom.app Δ =
      (S.a x.1).hom ≫ (Scheme.Etale.forget c.pt).map (U.inclusion x.1 ≫
        U.simplicial.map (SimplexCategory.Truncated.Hom.tr x.2.val Δ.unop.property
          (Nat.le_of_lt_succ x.1.isLt)).op) := by
  have nat := S.e.hom.naturality (SimplexCategory.Truncated.Hom.tr x.2.val Δ.unop.property
    (Nat.le_of_lt_succ x.1.isLt)).op
  simp only [Functor.comp_map] at nat
  rw [leg, Functor.map_comp, Category.assoc, nat, reassoc_of% (S.hι x.1), Functor.map_comp]
  rfl

/-- The diagram at the stage, as a diagram of qcqs étale schemes. -/
noncomputable def GQ : (SimplexCategory.Truncated r)ᵒᵖ ⥤ qcqsEtale.Over ⊤ (D.obj i) :=
  MorphismProperty.Comma.lift S.G (fun a ↦ (S.hG a).qcqsEtale) (fun _ ↦ trivial)
    (fun _ ↦ trivial)

/-- The `n`-th matching object at the stage. -/
noncomputable def M (n : Fin (r + 1)) : Over (D.obj i) :=
  (MorphismProperty.Over.forget _ _ _).obj (limit (matchingDiagram S.GQ n.val))

lemma isQcqsEtale_M (n : Fin (r + 1)) : IsQcqsEtale (S.M n) :=
  isQcqsEtale_of_qcqsEtale (limit (matchingDiagram S.GQ n.val)).prop

/-- The projections of the `n`-th matching object at the stage. -/
noncomputable def proj (n : Fin (r + 1)) (Δ : SimplexCategory.Truncated r)
    (h : Δ.obj.len < n.val) (θ : Δ.obj ⟶ SimplexCategory.mk n.val) :
    S.M n ⟶ S.G.obj (op Δ) :=
  (MorphismProperty.Over.forget _ _ _).map (limit.π (matchingDiagram S.GQ n.val) (op ⟨Δ, h, θ⟩))

lemma proj_nat (n : Fin (r + 1)) (Δ Δ' : SimplexCategory.Truncated r)
    (h : Δ.obj.len < n.val) (h' : Δ'.obj.len < n.val) (α : Δ' ⟶ Δ)
    (θ : Δ.obj ⟶ SimplexCategory.mk n.val) :
    S.proj n Δ h θ ≫ S.G.map α.op = S.proj n Δ' h' (α.hom ≫ θ) := by
  have := limit.w (matchingDiagram S.GQ n.val) (MatchingIndex.homMk h h' α θ).op
  exact congrArg (MorphismProperty.Over.forget _ _ _).map this

/-- The matching object at the stage is a limit. -/
noncomputable def isLimitM (n : Fin (r + 1)) :
    IsLimit (matchingCone S.G n.val (S.M n) (S.proj n) (S.proj_nat n)) :=
  isLimitOfPreserves (MorphismProperty.Over.forget _ _ _)
    (limit.isLimit (matchingDiagram S.GQ n.val))

lemma top_nat (n : Fin (r + 1)) (Δ Δ' : SimplexCategory.Truncated r)
    (_ : Δ.obj.len < n.val) (_ : Δ'.obj.len < n.val) (α : Δ' ⟶ Δ)
    (θ : Δ.obj ⟶ SimplexCategory.mk n.val) :
    S.G.map (SimplexCategory.Truncated.Hom.tr θ Δ.property (Nat.le_of_lt_succ n.isLt)).op ≫
        S.G.map α.op =
      S.G.map (SimplexCategory.Truncated.Hom.tr (α.hom ≫ θ) Δ'.property
        (Nat.le_of_lt_succ n.isLt)).op := by
  rw [← Functor.map_comp]
  rfl

/-- The `n`-th matching map at the stage. -/
noncomputable def mm (n : Fin (r + 1)) : S.G.obj (op (truncTop n)) ⟶ S.M n :=
  (S.isLimitM n).lift (matchingCone S.G n.val _ (fun Δ _ θ ↦ S.G.map
    (SimplexCategory.Truncated.Hom.tr θ Δ.property (Nat.le_of_lt_succ n.isLt)).op) (S.top_nat n))

lemma mm_proj (n : Fin (r + 1)) (Δ : SimplexCategory.Truncated r) (h : Δ.obj.len < n.val)
    (θ : Δ.obj ⟶ SimplexCategory.mk n.val) :
    S.mm n ≫ S.proj n Δ h θ = S.G.map
      (SimplexCategory.Truncated.Hom.tr θ Δ.property (Nat.le_of_lt_succ n.isLt)).op :=
  (S.isLimitM n).fac _ (op ⟨Δ, h, θ⟩)

end HypercoverStageData
namespace HypercoverStageData

variable [IsCofiltered I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] (hc : IsLimit c)
  {i : I} (S : HypercoverStageData D c U i)

include hc in
/-- The splitting cofans at the stage become coproducts at all sufficiently late stages. -/
theorem stageEventually_splitting :
    StageEventually i (fun _ h ↦ ∀ Δ : (SimplexCategory.Truncated r)ᵒᵖ,
      Nonempty (IsColimit (Cofan.mk ((Over.pullback (D.map h)).obj (S.G.obj Δ)).left
        fun x : SplitIndex Δ ↦ ((Over.pullback (D.map h)).map (S.leg Δ x)).left))) := by
  refine StageEventually.finite_forall fun Δ ↦ ?_
  let Al : SplitIndex Δ → Scheme.{u} := fun x : SplitIndex Δ ↦ (S.N x.1).left
  let p : ∀ x : SplitIndex Δ, Al x ⟶ D.obj i := fun x ↦ (S.N x.1).hom
  let W : Over (D.obj i) := Over.mk (Sigma.desc p)
  let ℓ : ∀ x : SplitIndex Δ, S.N x.1 ⟶ W := fun x ↦
    Over.homMk (Sigma.ι Al x) (Sigma.ι_desc p x)
  have hs : IsColimit (Cofan.mk W.left fun x ↦ (ℓ x).left) := coproductIsCoproduct Al
  let w : W ⟶ S.G.obj Δ := Over.homMk (Sigma.desc fun x ↦ (S.leg Δ x).left)
    (Sigma.hom_ext _ _ fun x ↦ by
      rw [Sigma.ι_desc_assoc]
      exact (Over.w (S.leg Δ x)).trans (Sigma.ι_desc p x).symm)
  have hℓw : ∀ x, ℓ x ≫ w = S.leg Δ x := fun x ↦ by
    apply Over.OverMorphism.ext
    exact Sigma.ι_desc (fun y : SplitIndex Δ ↦ (S.leg Δ y).left) x
  have hcomp : ∀ x, CompactSpace (Al x) := fun x ↦ by
    obtain ⟨_, _, _, _⟩ := S.hN x.1
    exact QuasiCompact.compactSpace_of_compactSpace (S.N x.1).hom
  have hqs : ∀ x, QuasiSeparatedSpace (Al x) := fun x ↦ by
    obtain ⟨_, _, _, _⟩ := S.hN x.1
    exact quasiSeparatedSpace_of_quasiSeparated (S.N x.1).hom
  obtain ⟨hW₁, hW₂⟩ := Scheme.compactSpace_quasiSeparatedSpace_of_isColimit (Sigma.ι Al)
    (coproductIsCoproduct Al)
  have het : Etale W.hom := IsZariskiLocalAtSource.sigmaDesc fun x ↦ (S.hN x.1).1
  have hW : IsQcqsEtale W :=
    ⟨het, inferInstance, @quasiCompact_of_compactSpace _ _ W.hom hW₁ _,
      @QuasiSeparated.of_quasiSeparatedSpace _ _ W.hom hW₂⟩
  have hP := (Over.nonempty_isColimit_pullback_cofan_left (c.π.app i) ℓ hs).some
  have hQ : IsColimit (Cofan.mk ((Over.pullback (c.π.app i)).obj (S.G.obj Δ)).left
      fun x : SplitIndex Δ ↦ ((Over.pullback (c.π.app i)).map (S.leg Δ x)).left) :=
    Cofan.isColimitOfIsos (Scheme.Etale.isColimitCofanLeft _ (U.splitting Δ))
      (fun x ↦ (Over.forget _).mapIso (S.a x.1)) ((Over.forget _).mapIso (S.e.app Δ))
      (fun x ↦ congrArg (fun φ ↦ φ.left) (S.leg_e Δ x))
  have hwl : ((Over.pullback (c.π.app i)).map w).left =
      (hP.coconePointUniqueUpToIso hQ).hom := by
    refine Cofan.IsColimit.hom_ext hP _ _ fun x ↦ ?_
    have := hP.comp_coconePointUniqueUpToIso_hom hQ ⟨x⟩
    simp only [Cofan.mk_pt, Cofan.mk_ι_app] at this
    change ((Over.pullback (c.π.app i)).map (ℓ x)).left ≫ _ = _
    refine Eq.trans ?_ this.symm
    rw [← Over.comp_left, ← Functor.map_comp, hℓw]
  have : IsIso ((Over.forget _).map ((Over.pullback (c.π.app i)).map w)) := by
    rw [Over.forget_map, hwl]
    infer_instance
  have : IsIso ((Over.pullback (c.π.app i)).map w) :=
    isIso_of_reflects_iso _ (Over.forget _)
  refine (stageEventually_isIso D hc hW (S.hG Δ) w).mono fun j h hh ↦ ⟨?_⟩
  refine Cofan.isColimitOfIsos
    (Over.nonempty_isColimit_pullback_cofan_left (D.map h) ℓ hs).some (fun x ↦ Iso.refl _)
    ((Over.forget _).mapIso (asIso ((Over.pullback (D.map h)).map w)).symm) fun x ↦ ?_
  change _ ≫ (inv ((Over.pullback (D.map h)).map w)).left = 𝟙 _ ≫ _
  rw [Category.id_comp, ← Over.comp_left, ← hℓw, Functor.map_comp, Category.assoc,
    IsIso.hom_inv_id, Category.comp_id]

include hc in
/-- The matching maps at the stage become surjective at all sufficiently late stages. -/
theorem stageEventually_surjective (n : Fin (r + 1)) :
    StageEventually i (fun _ h ↦ Surjective ((Over.pullback (D.map h)).map (S.mm n)).left) := by
  have hpb := isLimitOfPreserves (Over.pullback (c.π.app i)) (S.isLimitM n)
  have hU : IsLimit (matchingCone U.diagram n.val ((Scheme.Etale.forget c.pt).obj (U.matching n))
      (fun Δ h θ ↦ ((Scheme.Etale.forget c.pt).map (U.projection n Δ h θ) :
        _ ⟶ U.diagram.obj (op Δ))) (fun Δ Δ' h h' α θ ↦ by
        exact (Functor.map_comp (Scheme.Etale.forget c.pt) _ _).symm.trans
          (congrArg _ (U.projection_naturality n Δ Δ' h h' α θ)))) :=
    isLimitMatchingCone fun T p hp ↦ U.matching_universal n T p hp
  let β : matchingDiagram S.G n.val ⋙ Over.pullback (c.π.app i) ≅
      matchingDiagram U.diagram n.val :=
    NatIso.ofComponents (fun q ↦ S.e.app (op q.unop.obj)) fun f ↦ S.e.hom.naturality _
  let φ := hpb.conePointsIsoOfNatIso hU β
  have key : (Over.pullback (c.π.app i)).map (S.mm n) ≫ φ.hom =
      S.e.hom.app (op (truncTop n)) ≫ (Scheme.Etale.forget c.pt).map (U.matchingMap n) := by
    refine hU.hom_ext fun q ↦ ?_
    have h₁ := hpb.conePointsIsoOfNatIso_hom_comp hU β q
    have h₂ := S.e.hom.naturality (SimplexCategory.Truncated.Hom.tr q.unop.hom
      q.unop.obj.property (Nat.le_of_lt_succ n.isLt)).op
    simp only [Functor.comp_map] at h₂
    simp only [Category.assoc]
    erw [h₁]
    change _ ≫ (Over.pullback (c.π.app i)).map (S.proj n _ _ _) ≫ S.e.hom.app _ = _ ≫
      (Scheme.Etale.forget c.pt).map (U.matchingMap n) ≫
        (Scheme.Etale.forget c.pt).map (U.projection n _ _ _)
    rw [← Functor.map_comp_assoc, S.mm_proj, h₂, ← Functor.map_comp, U.matchingMap_projection]
    rfl
  have hsurj : Surjective ((Over.pullback (c.π.app i)).map (S.mm n)).left := by
    refine ⟨fun x ↦ ?_⟩
    obtain ⟨z, hz⟩ := (U.matching_cover n).surj (φ.hom.left x)
    refine ⟨(S.e.inv.app (op (truncTop n))).left z, φ.hom.left.homeomorph.injective ?_⟩
    change (((Over.pullback (c.π.app i)).map (S.mm n)).left ≫ φ.hom.left)
      ((S.e.inv.app (op (truncTop n))).left z) = φ.hom.left x
    have hz' : (S.e.hom.app (op (truncTop n))).left ((S.e.inv.app (op (truncTop n))).left z) =
        z := by
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, Iso.inv_hom_id_app]
      rfl
    rw [← Over.comp_left, key, Over.comp_left, Scheme.Hom.comp_apply]
    exact (congrArg _ hz').trans hz
  obtain ⟨i₁, h₁, H⟩ := exists_stage_jointly_surjective D hc (Finset.univ : Finset Unit)
    (S.M n) (fun _ ↦ S.G.obj (op (truncTop n))) (fun _ ↦ S.mm n) (S.isQcqsEtale_M n)
    (fun _ ↦ S.hG _) fun x ↦ by
      obtain ⟨y, hy⟩ := hsurj.surj x
      exact ⟨(), Finset.mem_univ _, y, hy⟩
  refine ⟨i₁, h₁, fun j g ↦ ⟨fun x ↦ ?_⟩⟩
  obtain ⟨_, _, y, hy⟩ := H j g x
  exact ⟨y, hy⟩

end HypercoverStageData
namespace HypercoverStageData

variable [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] {i : I}
  (S : HypercoverStageData D c U i)

/-- The truncated finite split étale hypercover at a stage where the splitting cofans are
coproducts and the matching maps are surjective. -/
noncomputable def toHypercover {j : I} (h : j ⟶ i)
    (Hsplit : ∀ Δ : (SimplexCategory.Truncated r)ᵒᵖ,
      Nonempty (IsColimit (Cofan.mk ((Over.pullback (D.map h)).obj (S.G.obj Δ)).left
        fun x : SplitIndex Δ ↦ ((Over.pullback (D.map h)).map (S.leg Δ x)).left)))
    (Hsurj : ∀ n, Surjective ((Over.pullback (D.map h)).map (S.mm n)).left) :
    TruncatedFiniteSplitEtaleHypercover (D.obj j) r where
  simplicial := MorphismProperty.Comma.lift (S.G ⋙ Over.pullback (D.map h))
    (fun a ↦ ((S.hG a).overPullback (D.map h)).1) (fun _ ↦ trivial) (fun _ ↦ trivial)
  N n := MorphismProperty.Over.mk ⊤ ((Over.pullback (D.map h)).obj (S.N n)).hom
    ((S.hN n).overPullback (D.map h)).1
  inclusion n := MorphismProperty.Over.homMk ((Over.pullback (D.map h)).map (S.ι n)).left
    (Over.w _)
  splitting Δ := Scheme.Etale.isColimitOfCofanLeft _ (Cofan.isColimitCongr
    (fun x ↦ by rw [leg, Functor.map_comp, Over.comp_left]; rfl) (Hsplit Δ).some)
  finite_each_degree n := by
    obtain ⟨_, _, _, _⟩ := (S.hN n).overPullback (D.map h)
    exact ⟨1, fun _ ↦ MorphismProperty.Over.mk ⊤ ((Over.pullback (D.map h)).obj (S.N n)).hom
      ((S.hN n).overPullback (D.map h)).1, fun _ ↦ 𝟙 _, ⟨Cofan.isColimitId _⟩, fun _ ↦
      ⟨QuasiCompact.compactSpace_of_compactSpace ((Over.pullback (D.map h)).obj (S.N n)).hom,
        quasiSeparatedSpace_of_quasiSeparated ((Over.pullback (D.map h)).obj (S.N n)).hom,
        ‹_›, ‹_›, ‹_›⟩⟩
  matching n := MorphismProperty.Over.mk ⊤ ((Over.pullback (D.map h)).obj (S.M n)).hom
    ((S.isQcqsEtale_M n).overPullback (D.map h)).1
  projection n Δ hlt θ := MorphismProperty.Over.homMk
    ((Over.pullback (D.map h)).map (S.proj n Δ hlt θ)).left (Over.w _)
  projection_naturality n Δ Δ' hlt hlt' α θ := MorphismProperty.Over.Hom.ext (by
    change ((Over.pullback (D.map h)).map (S.proj n Δ hlt θ)).left ≫
      ((Over.pullback (D.map h)).map (S.G.map α.op)).left =
        ((Over.pullback (D.map h)).map (S.proj n Δ' hlt' (α.hom ≫ θ))).left
    rw [← Over.comp_left, ← Functor.map_comp, S.proj_nat])
  matching_universal n T p hp := matchingCone_universal (K := S.G ⋙ Over.pullback (D.map h))
    (M := (Over.pullback (D.map h)).obj (S.M n))
    (proj := fun Δ hlt θ ↦ (Over.pullback (D.map h)).map (S.proj n Δ hlt θ))
    (nat := fun Δ Δ' hlt hlt' α θ ↦ by
      rw [Functor.comp_map, ← Functor.map_comp, S.proj_nat])
    (isLimitOfPreserves (Over.pullback (D.map h)) (S.isLimitM n)) T p hp
  matchingMap n := MorphismProperty.Over.homMk
    ((Over.pullback (D.map h)).map (S.mm n)).left (Over.w _)
  matchingMap_projection n Δ hlt θ := MorphismProperty.Over.Hom.ext (by
    change ((Over.pullback (D.map h)).map (S.mm n)).left ≫
      ((Over.pullback (D.map h)).map (S.proj n Δ hlt θ)).left =
        ((Over.pullback (D.map h)).map (S.G.map (SimplexCategory.Truncated.Hom.tr θ Δ.property
          (Nat.le_of_lt_succ n.isLt)).op)).left
    rw [← Over.comp_left, ← Functor.map_comp, S.mm_proj])
  matching_cover n := Hsurj n

lemma isBaseChange_toHypercover {j : I} (h : j ⟶ i)
    (Hsplit : ∀ Δ : (SimplexCategory.Truncated r)ᵒᵖ,
      Nonempty (IsColimit (Cofan.mk ((Over.pullback (D.map h)).obj (S.G.obj Δ)).left
        fun x : SplitIndex Δ ↦ ((Over.pullback (D.map h)).map (S.leg Δ x)).left)))
    (Hsurj : ∀ n, Surjective ((Over.pullback (D.map h)).map (S.mm n)).left) :
    (S.toHypercover h Hsplit Hsurj).IsBaseChange (c.π.app j) U :=
  ⟨Functor.isoWhiskerLeft S.G (overPullbackStageIso D c h) ≪≫ S.e, fun n ↦
    ⟨(overPullbackStageIso D c h).app (S.N n) ≪≫ S.a n, (S.transport h).hι n⟩⟩

end HypercoverStageData

variable [IsCofiltered I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] (hc : IsLimit c)

include hc in
/-- A truncated finite split étale hypercover of the limit of a cofiltered system of qcqs
schemes with affine transition maps is the base change of one at some stage. -/
theorem exists_truncatedFiniteSplitEtaleHypercover_isBaseChange
    (U : TruncatedFiniteSplitEtaleHypercover c.pt r) :
    ∃ (j : I) (Ui : TruncatedFiniteSplitEtaleHypercover (D.obj j) r),
      Ui.IsBaseChange (c.π.app j) U := by
  obtain ⟨i, ⟨S⟩⟩ := exists_hypercoverStageData D U hc
  obtain ⟨j, h, Hsplit, Hsurj⟩ := ((S.stageEventually_splitting hc).and
    (StageEventually.finite_forall fun n ↦ S.stageEventually_surjective hc n)).exists_hom
  exact ⟨j, S.toHypercover h Hsplit Hsurj, S.isBaseChange_toHypercover h Hsplit Hsurj⟩

end AlgebraicGeometry
