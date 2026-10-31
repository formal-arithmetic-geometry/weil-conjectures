/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CurrentIntegralData
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Integral compositor descent along reduction

Source: latest blueprint, sec-smooth-purity, composition-comparisons, integral clause.
(blueprint: lem-sp-current-integral-composition-laws).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.CompositionComparisons
open IntegralDirectImageTower NormalizedIntegralAdjunction

section Descent
universe uc1 uc2 uc3 ud1 ud2 ud3 vc1 vc2 vc3 vd1 vd2 vd3
variable {C₁ : Type uc1} {C₂ : Type uc2} {C₃ : Type uc3}
  {D₁ : Type ud1} {D₂ : Type ud2} {D₃ : Type ud3}
  [Category.{vc1} C₁] [Category.{vc2} C₂] [Category.{vc3} C₃]
  [Category.{vd1} D₁] [Category.{vd2} D₂] [Category.{vd3} D₃]

private structure Evaluation (E₁ : C₁ ⥤ D₁) (E₂ : C₂ ⥤ D₂)
    {F : C₁ ⥤ C₂} {RF : C₂ ⥤ C₁} (aF : F ⊣ RF)
    {f : D₁ ⥤ D₂} {rf : D₂ ⥤ D₁} (af : f ⊣ rf) where
  left : F ⋙ E₂ ≅ E₁ ⋙ f
  right : RF ⋙ E₁ ≅ E₂ ⋙ rf
  unit : ∀ M, E₁.map (aF.unit.app M) ≫ right.hom.app (F.obj M) ≫
    rf.map (left.hom.app M) = af.unit.app (E₁.obj M)
  counit : ∀ K, f.map (right.hom.app K) ≫ af.counit.app (E₂.obj K) =
    left.inv.app (RF.obj K) ≫ E₂.map (aF.counit.app K)

private theorem evaluation_transpose
    {E₁ : C₁ ⥤ D₁} {E₂ : C₂ ⥤ D₂}
    {L : C₁ ⥤ C₂} {R : C₂ ⥤ C₁} {l : D₁ ⥤ D₂} {r : D₂ ⥤ D₁}
    (adj : L ⊣ R) (level : l ⊣ r) (A : Evaluation E₁ E₂ adj level)
    {P : C₁} {Q : C₂} (f : L.obj P ⟶ Q) :
    E₁.map (adj.homEquiv _ _ f) ≫ A.right.hom.app Q =
      level.homEquiv _ _ (A.left.inv.app P ≫ E₂.map f) := by
  rw [adj.homEquiv_unit, level.homEquiv_unit]
  simp only [Functor.map_comp, Category.assoc]
  have hr := A.right.hom.naturality f
  dsimp only [Functor.comp_map] at hr
  rw [hr]
  have hu : E₁.map (adj.unit.app P) ≫ A.right.hom.app (L.obj P) =
      level.unit.app (E₁.obj P) ≫ r.map (A.left.inv.app P) := by
    rw [← A.unit P]
    have hi := (r.mapIso (A.left.app P)).hom_inv_id
    change r.map (A.left.hom.app P) ≫ r.map (A.left.inv.app P) = 𝟙 _ at hi
    simp only [Category.assoc, hi]
    erw [Category.comp_id]
  rw [← Category.assoc, hu, Category.assoc]

private theorem evaluated_compositor
    {F : C₁ ⥤ C₂} {G : C₂ ⥤ C₃} {H : C₁ ⥤ C₃}
    {RF : C₂ ⥤ C₁} {RG : C₃ ⥤ C₂} {RH : C₃ ⥤ C₁}
    {f : D₁ ⥤ D₂} {g : D₂ ⥤ D₃} {h : D₁ ⥤ D₃}
    {rf : D₂ ⥤ D₁} {rg : D₃ ⥤ D₂} {rh : D₃ ⥤ D₁}
    {E₁ : C₁ ⥤ D₁} {E₂ : C₂ ⥤ D₂} {E₃ : C₃ ⥤ D₃}
    (aF : F ⊣ RF) (aG : G ⊣ RG) (aH : H ⊣ RH)
    (af : f ⊣ rf) (ag : g ⊣ rg) (ah : h ⊣ rh)
    (AF : Evaluation E₁ E₂ aF af)
    (AG : Evaluation E₂ E₃ aG ag)
    (AH : Evaluation E₁ E₃ aH ah)
    (alpha : F ⋙ G ≅ H) (alphaₙ : f ⋙ g ≅ h)
    (theta : RH ≅ RG ⋙ RF) (thetaₙ : rh ≅ rg ⋙ rf)
    (hc : ∀ K, (F ⋙ G).map (theta.hom.app K) ≫ (aF.comp aG).counit.app K =
      alpha.hom.app (RH.obj K) ≫ aH.counit.app K)
    (hcn : ∀ K, (f ⋙ g).map (thetaₙ.hom.app K) ≫ (af.comp ag).counit.app K =
      alphaₙ.hom.app (rh.obj K) ≫ ah.counit.app K)
    (ha : ∀ M, E₃.map (alpha.hom.app M) ≫ AH.left.hom.app M =
      AG.left.hom.app (F.obj M) ≫ g.map (AF.left.hom.app M) ≫
        alphaₙ.hom.app (E₁.obj M)) (K : C₃) :
    E₁.map (theta.hom.app K) ≫ AF.right.hom.app (RG.obj K) ≫
        rf.map (AG.right.hom.app K) =
      AH.right.hom.app K ≫ thetaₙ.hom.app (E₃.obj K) := by
  have ht : theta.hom.app K = (aF.comp aG).homEquiv _ _
      (alpha.hom.app (RH.obj K) ≫ aH.counit.app K) := by
    apply ((aF.comp aG).homEquiv _ _).symm.injective
    dsimp only [Functor.id_obj, Functor.comp_obj]
    rw [Equiv.symm_apply_apply]
    change (F ⋙ G).map (theta.hom.app K) ≫ (aF.comp aG).counit.app K = _
    exact hc K
  have hl : E₁.map (theta.hom.app K) ≫ AF.right.hom.app (RG.obj K) ≫
      rf.map (AG.right.hom.app K) =
      (af.comp ag).homEquiv _ _
        (g.map (AF.left.inv.app (RH.obj K)) ≫ AG.left.inv.app (F.obj (RH.obj K)) ≫
          E₃.map (alpha.hom.app (RH.obj K) ≫ aH.counit.app K)) := by
    rw [ht, Adjunction.comp_homEquiv, Adjunction.comp_homEquiv]
    change E₁.map (aF.homEquiv _ _ (aG.homEquiv _ _ _)) ≫ _ =
      af.homEquiv _ _ (ag.homEquiv _ _ _)
    dsimp only [Functor.id_obj, Functor.comp_obj]
    have hF := evaluation_transpose aF af AF (P := RH.obj K) (Q := RG.obj K)
      (aG.homEquiv (F.obj (RH.obj K)) K (alpha.hom.app (RH.obj K) ≫ aH.counit.app K))
    have hG := evaluation_transpose aG ag AG (P := F.obj (RH.obj K)) (Q := K)
      (alpha.hom.app (RH.obj K) ≫ aH.counit.app K)
    dsimp only [Functor.comp_obj, Functor.id_obj] at hF hG
    rw [← Category.assoc, hF]
    rw [← af.homEquiv_naturality_right, Category.assoc, hG,
      ← ag.homEquiv_naturality_left]
  have hr : AH.right.hom.app K ≫ thetaₙ.hom.app (E₃.obj K) =
      (af.comp ag).homEquiv _ _
        (alphaₙ.hom.app (E₁.obj (RH.obj K)) ≫ AH.left.inv.app (RH.obj K) ≫
          E₃.map (aH.counit.app K)) := by
    apply ((af.comp ag).homEquiv _ _).symm.injective
    dsimp only [Functor.id_obj, Functor.comp_obj]
    rw [Equiv.symm_apply_apply]
    change (f ⋙ g).map (AH.right.hom.app K ≫ thetaₙ.hom.app (E₃.obj K)) ≫
      (af.comp ag).counit.app (E₃.obj K) = _
    rw [Functor.map_comp, Category.assoc, hcn]
    change (f ⋙ g).map (AH.right.hom.app K) ≫
      alphaₙ.hom.app _ ≫ ah.counit.app _ = _
    rw [alphaₙ.hom.naturality_assoc, AH.counit K]
    rfl
  rw [hl, hr]
  congr 1
  let B := AG.left.app (F.obj (RH.obj K)) ≪≫ g.mapIso (AF.left.app (RH.obj K))
  have hA : E₃.map (alpha.hom.app (RH.obj K)) ≫ AH.left.hom.app (RH.obj K) =
      B.hom ≫ alphaₙ.hom.app (E₁.obj (RH.obj K)) := by
    simpa only [B, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc] using
      ha (RH.obj K)
  have hw' : g.map (AF.left.inv.app (RH.obj K)) ≫ AG.left.inv.app (F.obj (RH.obj K)) ≫
      E₃.map (alpha.hom.app (RH.obj K)) =
      alphaₙ.hom.app (E₁.obj (RH.obj K)) ≫ AH.left.inv.app (RH.obj K) := by
    have he : B.inv ≫ E₃.map (alpha.hom.app (RH.obj K)) =
        alphaₙ.hom.app (E₁.obj (RH.obj K)) ≫ AH.left.inv.app (RH.obj K) := by
      calc
        _ = B.inv ≫ (E₃.map (alpha.hom.app (RH.obj K)) ≫
            AH.left.hom.app (RH.obj K)) ≫ AH.left.inv.app (RH.obj K) := by
          simp only [Category.assoc, Iso.hom_inv_id_app]
          dsimp only [Functor.comp_obj]
          rw [Category.comp_id]
        _ = B.inv ≫ (B.hom ≫ alphaₙ.hom.app (E₁.obj (RH.obj K))) ≫
            AH.left.inv.app (RH.obj K) := by rw [hA]
        _ = _ := by
          have hi := B.inv_hom_id_assoc (alphaₙ.hom.app (E₁.obj (RH.obj K)))
          dsimp only [Functor.comp_obj] at hi ⊢
          simpa only [Category.assoc] using
            congrArg (fun t ↦ t ≫ AH.left.inv.app (RH.obj K)) hi
    simpa only [B, Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Category.assoc] using he
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (fun t ↦ t ≫ E₃.map (aH.counit.app K)) hw'

private theorem composition_of_fully_faithful_reductions_general
    {F : C₁ ⥤ C₂} {G : C₂ ⥤ C₃} {H : C₁ ⥤ C₃}
    {RF : C₂ ⥤ C₁} {RG : C₃ ⥤ C₂} {RH : C₃ ⥤ C₁}
    {f : D₁ ⥤ D₂} {g : D₂ ⥤ D₃} {h : D₁ ⥤ D₃}
    {rf : D₂ ⥤ D₁} {rg : D₃ ⥤ D₂} {rh : D₃ ⥤ D₁}
    {E₁ : C₁ ⥤ D₁} {E₂ : C₂ ⥤ D₂} {E₃ : C₃ ⥤ D₃}
    (aF : F ⊣ RF) (aG : G ⊣ RG) (aH : H ⊣ RH)
    (af : f ⊣ rf) (ag : g ⊣ rg) (ah : h ⊣ rh)
    (AF : Evaluation E₁ E₂ aF af)
    (AG : Evaluation E₂ E₃ aG ag)
    (AH : Evaluation E₁ E₃ aH ah)
    (full : E₃.FullyFaithful) (alphaₙ : f ⋙ g ≅ h) (thetaₙ : rh ≅ rg ⋙ rf)
    (hcₙ : ∀ K, (f ⋙ g).map (thetaₙ.hom.app K) ≫ (af.comp ag).counit.app K =
      alphaₙ.hom.app (rh.obj K) ≫ ah.counit.app K) :
    ∃ alpha : F ⋙ G ≅ H, ∃ theta : RH ≅ RG ⋙ RF,
      SpCompositionIntegralLaws F G H RF RG RH aF aG aH E₁ E₂ E₃ f g h rf rg rh
        AF.left AG.left AH.left AF.right AG.right AH.right alphaₙ thetaₙ alpha theta := by
  let beta : (F ⋙ G) ⋙ E₃ ≅ H ⋙ E₃ :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft F AG.left ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight AF.left g ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft E₁ alphaₙ ≪≫ AH.left.symm
  let alpha : F ⋙ G ≅ H := (full.whiskeringRight C₁).preimageIso beta
  have ha (M : C₁) : E₃.map (alpha.hom.app M) ≫ AH.left.hom.app M =
      AG.left.hom.app (F.obj M) ≫ g.map (AF.left.hom.app M) ≫
        alphaₙ.hom.app (E₁.obj M) := by
    have hp := congrArg (fun t ↦ t.app M)
      ((full.whiskeringRight C₁).map_preimage beta.hom)
    change E₃.map (alpha.hom.app M) = beta.hom.app M at hp
    rw [hp]
    simp [beta, Category.assoc]
  let theta := (aH.ofNatIsoLeft alpha.symm).rightAdjointUniq (aF.comp aG)
  have hc (K : C₃) : (F ⋙ G).map (theta.hom.app K) ≫ (aF.comp aG).counit.app K =
      alpha.hom.app (RH.obj K) ≫ aH.counit.app K :=
    (aH.ofNatIsoLeft alpha.symm).rightAdjointUniq_hom_app_counit (aF.comp aG) K
  refine ⟨alpha, theta, ⟨ha, ?_, hc, ?_, ?_⟩⟩
  · exact evaluated_compositor aF aG aH af ag ah AF AG AH
      alpha alphaₙ theta thetaₙ hc hcₙ ha
  · intro t ht
    ext K
    apply ((aF.comp aG).homEquiv _ _).symm.injective
    simpa only [Adjunction.homEquiv_counit] using (ht K).trans (hc K).symm
  · exact fun K ↦ (aF.comp_counit_app aG K).symm

end Descent

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The three integral edge comparisons descend both tower compositors and their laws.
Source: latest blueprint, composition-comparisons proof, final paragraph.
(blueprint: lem-sp-current-integral-composition-laws).

Proof: compose the three left comparisons with the tower compositor and lift through
fully faithful reduction. Form the right compositor by uniqueness of the right adjoint
to the resulting composite left adjoint. Naturality and the unit/counit equations for
each edge identify its reduction with the specified tower right compositor. Transposition
through the composite Hom equivalence proves uniqueness and its counit normalization. -/
theorem integralLaws
    (s : Presentation l (ULift.{u} (Padic l)))
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (cf : Compactification f) (cg : Compactification g) (ch : Compactification (f ≫ g))
    (hFf : ∀ M : Towers l (ULift.{u} (Padic l)) s X,
      spConstructibleTorTowers l (ULift.{u} (Padic l)) Y (s.towers Y)
        ((towerShriek l (ULift.{u} (Padic l)) s cf).obj M.obj))
    (hFg : ∀ M : Towers l (ULift.{u} (Padic l)) s Y,
      spConstructibleTorTowers l (ULift.{u} (Padic l)) Z (s.towers Z)
        ((towerShriek l (ULift.{u} (Padic l)) s cg).obj M.obj))
    (hFh : ∀ M : Towers l (ULift.{u} (Padic l)) s X,
      spConstructibleTorTowers l (ULift.{u} (Padic l)) Z (s.towers Z)
        ((towerShriek l (ULift.{u} (Padic l)) s ch).obj M.obj))
    (Gf : Towers l (ULift.{u} (Padic l)) s Y ⥤ Towers l (ULift.{u} (Padic l)) s X)
    (Gg : Towers l (ULift.{u} (Padic l)) s Z ⥤ Towers l (ULift.{u} (Padic l)) s Y)
    (Gh : Towers l (ULift.{u} (Padic l)) s Z ⥤ Towers l (ULift.{u} (Padic l)) s X)
    (af : towerSupport l (ULift.{u} (Padic l)) s cf hFf ⊣ Gf)
    (ag : towerSupport l (ULift.{u} (Padic l)) s cg hFg ⊣ Gg)
    (ah : towerSupport l (ULift.{u} (Padic l)) s ch hFh ⊣ Gh)
    (If : IntegralEdge l (ULift.{u} (Padic l)) s cf hFf Gf af)
    (Ig : IntegralEdge l (ULift.{u} (Padic l)) s cg hFg Gg ag)
    (Ih : IntegralEdge l (ULift.{u} (Padic l)) s ch hFh Gh ah)
    (full : (reduction l (ULift.{u} (Padic l)) s Z Ih.reductionY).FullyFaithful)
    (alphaTower : towerSupport l (ULift.{u} (Padic l)) s cf hFf ⋙
        towerSupport l (ULift.{u} (Padic l)) s cg hFg ≅
      towerSupport l (ULift.{u} (Padic l)) s ch hFh)
    (thetaTower : Gh ≅ Gg ⋙ Gf)
    (_ht : ∀ K,
      (towerSupport l (ULift.{u} (Padic l)) s cf hFf ⋙
          towerSupport l (ULift.{u} (Padic l)) s cg hFg).map (thetaTower.hom.app K) ≫
        (af.comp ag).counit.app K = alphaTower.hom.app (Gh.obj K) ≫ ah.counit.app K) :
    ∃ alpha : support l (ULift.{u} (Padic l)) cf If.supportClosed ⋙
        support l (ULift.{u} (Padic l)) cg Ig.supportClosed ≅
      support l (ULift.{u} (Padic l)) ch Ih.supportClosed,
    ∃ theta : right l (ULift.{u} (Padic l)) s Ih.limitX Ih.reductionY Gh Ih.closed ≅
        right l (ULift.{u} (Padic l)) s Ig.limitX Ig.reductionY Gg Ig.closed ⋙
          right l (ULift.{u} (Padic l)) s If.limitX If.reductionY Gf If.closed,
      SpCompositionIntegralLaws
        (support l (ULift.{u} (Padic l)) cf If.supportClosed)
        (support l (ULift.{u} (Padic l)) cg Ig.supportClosed)
        (support l (ULift.{u} (Padic l)) ch Ih.supportClosed)
        (right l (ULift.{u} (Padic l)) s If.limitX If.reductionY Gf If.closed)
        (right l (ULift.{u} (Padic l)) s Ig.limitX Ig.reductionY Gg Ig.closed)
        (right l (ULift.{u} (Padic l)) s Ih.limitX Ih.reductionY Gh Ih.closed)
        If.adjunction Ig.adjunction Ih.adjunction
        (reduction l (ULift.{u} (Padic l)) s X If.reductionX)
        (reduction l (ULift.{u} (Padic l)) s Y Ig.reductionX)
        (reduction l (ULift.{u} (Padic l)) s Z Ih.reductionY)
        (towerSupport l (ULift.{u} (Padic l)) s cf hFf)
        (towerSupport l (ULift.{u} (Padic l)) s cg hFg)
        (towerSupport l (ULift.{u} (Padic l)) s ch hFh) Gf Gg Gh
        If.leftComparison Ig.leftComparison Ih.leftComparison
        If.rightComparison Ig.rightComparison Ih.rightComparison
        alphaTower thetaTower alpha theta := by
  apply composition_of_fully_faithful_reductions_general
    (F := support l (ULift.{u} (Padic l)) cf If.supportClosed)
    (G := support l (ULift.{u} (Padic l)) cg Ig.supportClosed)
    (H := support l (ULift.{u} (Padic l)) ch Ih.supportClosed)
    (RF := right l (ULift.{u} (Padic l)) s If.limitX If.reductionY Gf If.closed)
    (RG := right l (ULift.{u} (Padic l)) s Ig.limitX Ig.reductionY Gg Ig.closed)
    (RH := right l (ULift.{u} (Padic l)) s Ih.limitX Ih.reductionY Gh Ih.closed)
    (f := towerSupport l (ULift.{u} (Padic l)) s cf hFf)
    (g := towerSupport l (ULift.{u} (Padic l)) s cg hFg)
    (h := towerSupport l (ULift.{u} (Padic l)) s ch hFh)
    (rf := Gf) (rg := Gg) (rh := Gh)
    (E₁ := reduction l (ULift.{u} (Padic l)) s X If.reductionX)
    (E₂ := reduction l (ULift.{u} (Padic l)) s Y Ig.reductionX)
    (E₃ := reduction l (ULift.{u} (Padic l)) s Z Ih.reductionY)
    If.adjunction Ig.adjunction Ih.adjunction
    af ag ah
    (AF := {
      left := If.leftComparison
      right := If.rightComparison
      unit := ?_
      counit := ?_ })
    (AG := {
      left := Ig.leftComparison
      right := Ig.rightComparison
      unit := ?_
      counit := ?_ })
    (AH := {
      left := Ih.leftComparison
      right := Ih.rightComparison
      unit := ?_
      counit := ?_ })
    full alphaTower thetaTower _ht
  · intro M
    simp [If.unit_reduction, Category.assoc]
  · intro K
    rw [If.counit_reduction]
    simp
  · intro M
    simp [Ig.unit_reduction, Category.assoc]
  · intro K
    rw [Ig.counit_reduction]
    simp
  · intro M
    simp [Ih.unit_reduction, Category.assoc]
  · intro K
    rw [Ih.counit_reduction]
    simp

end AlgebraicGeometry.ProEtale.CompositionComparisons
