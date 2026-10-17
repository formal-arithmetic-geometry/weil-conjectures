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
  let ℓ : ∀ x, S.N x.1 ⟶ W := fun x ↦ Over.homMk (Sigma.ι Al x) (Sigma.ι_desc p x)
  have hs : IsColimit (Cofan.mk W.left fun x ↦ (ℓ x).left) := coproductIsCoproduct Al
  let w : W ⟶ S.G.obj Δ := Over.homMk (Sigma.desc fun x ↦ (S.leg Δ x).left)
    (Sigma.hom_ext _ _ fun x ↦ by
      rw [Sigma.ι_desc_assoc]
      exact (Over.w (S.leg Δ x)).trans (Sigma.ι_desc p x).symm)
  have hℓw : ∀ x, ℓ x ≫ w = S.leg Δ x := fun x ↦
    Over.OverMorphism.ext (Sigma.ι_desc (fun y : SplitIndex Δ ↦ (S.leg Δ y).left) x)
  have hcomp : ∀ x, CompactSpace (Al x) := fun x ↦ by
    obtain ⟨_, _, _, _⟩ := S.hN x.1
    exact QuasiCompact.compactSpace_of_compactSpace (S.N x.1).hom
  have hqs : ∀ x, QuasiSeparatedSpace (Al x) := fun x ↦ by
    obtain ⟨_, _, _, _⟩ := S.hN x.1
    exact quasiSeparatedSpace_of_quasiSeparated (S.N x.1).hom
  obtain ⟨hW₁, hW₂⟩ := Scheme.compactSpace_quasiSeparatedSpace_of_isColimit (Sigma.ι Al)
    (coproductIsCoproduct Al)
  have hW : IsQcqsEtale W :=
    ⟨IsZariskiLocalAtSource.sigmaDesc fun x ↦ (S.hN x.1).1, inferInstance,
      @quasiCompact_of_compactSpace _ _ W.hom hW₁ _,
      @QuasiSeparated.of_quasiSeparatedSpace _ _ W.hom hW₂⟩
  -- the base change of `w` to the limit is an isomorphism
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
    rw [this, ← Over.comp_left, ← Functor.map_comp, hℓw]
  have : IsIso ((Over.pullback (c.π.app i)).map w).left := by
    rw [hwl]
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
      (fun Δ h θ ↦ (Scheme.Etale.forget c.pt).map (U.projection n Δ h θ)) (fun Δ Δ' h h' α θ ↦ by
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
    rw [← Over.comp_left, key, Over.comp_left, ← Scheme.Hom.comp_apply, ← Category.assoc,
      ← Over.comp_left, Iso.inv_hom_id_app, Over.id_left, Category.id_comp]
    exact hz
  obtain ⟨i₁, h₁, H⟩ := exists_stage_jointly_surjective D hc (Finset.univ : Finset Unit)
    (S.M n) (fun _ ↦ S.G.obj (op (truncTop n))) (fun _ ↦ S.mm n) (S.isQcqsEtale_M n)
    (fun _ ↦ S.hG _) fun x ↦ by
      obtain ⟨y, hy⟩ := hsurj.surj x
      exact ⟨(), Finset.mem_univ _, y, hy⟩
  refine ⟨i₁, h₁, fun j g ↦ ⟨fun x ↦ ?_⟩⟩
  obtain ⟨_, _, y, hy⟩ := H j g x
  exact ⟨y, hy⟩

end HypercoverStageData

end AlgebraicGeometry
