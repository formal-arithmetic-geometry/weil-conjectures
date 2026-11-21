/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CoefficientConstructibleEtaleModules

/-! # Inverse image of finite module local systems

Source: Stacks Project, Sites, Tags 00YV and 00XZ.
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe w
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {C D : Type w} [SmallCategory C] [SmallCategory D]
  [HasFiniteLimits C] [HasFiniteLimits D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (G : C ⥤ D) [G.IsContinuous J K] [PreservesFiniteLimits G]
  (R : Type w) [CommRing R]

private instance preservesHypercovers : G.PreservesOneHypercovers J K :=
  Functor.PreservesOneHypercovers.of_coverPreserving
    (CoverPreserving.of_isContinuous G J K)

set_option backward.isDefEq.respectTransparency false in
private def starPostIso (X : C) :
    Over.star X ⋙ Over.post G ≅ G ⋙ Over.star (G.obj X) :=
  NatIso.ofComponents
    (fun Y ↦ Over.isoMk (asIso (prodComparison G X Y)) (by
      simp only [Functor.comp_obj, Over.star_obj_hom, asIso_hom,
        prodComparison_fst]
      change G.map prod.fst = G.map (prod.lift prod.fst (𝟙 _) ≫ prod.fst)
      rw [prod.lift_fst]))
    (by
      intro Y Z f
      apply Over.OverMorphism.ext
      change G.map (Limits.prod.map (𝟙 X) f) ≫ prodComparison G X Z =
        prodComparison G X Y ≫ Limits.prod.map (𝟙 (G.obj X)) (G.map f)
      simpa only [G.map_id] using prodComparison_natural G (𝟙 X) f)

private def restrictionAdjunction (X : C) :
    J.overPullback (ModuleCat.{w} R) X ⊣
      (Over.star X).sheafPushforwardContinuous (ModuleCat.{w} R) J (J.over X) :=
  (Over.forgetAdjStar X).sheafPushforwardContinuous (E := ModuleCat.{w} R) (J.over X) J

private def pullbackOverIso (X : C) :
    Functor.sheafPullbackConstruction.sheafPullback G (ModuleCat.{w} R) J K ⋙
        K.overPullback (ModuleCat.{w} R) (G.obj X) ≅
      J.overPullback (ModuleCat.{w} R) X ⋙
        Functor.sheafPullbackConstruction.sheafPullback (Over.post G)
          (ModuleCat.{w} R) (J.over X) (K.over (G.obj X)) := by
  let adj₁ :=
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous G
      (ModuleCat.{w} R) J K).comp (restrictionAdjunction K R (G.obj X))
  let adj₂ :=
    (restrictionAdjunction J R X).comp
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Over.post G)
        (ModuleCat.{w} R) (J.over X) (K.over (G.obj X)))
  let i₁ := Functor.sheafPushforwardContinuousComp G (Over.star (G.obj X))
    (ModuleCat.{w} R) J K (K.over (G.obj X))
  let i₂ := Functor.sheafPushforwardContinuousComp (Over.star X) (Over.post G)
    (ModuleCat.{w} R) J (J.over X) (K.over (G.obj X))
  letI := Functor.isContinuous_comp G (Over.star (G.obj X)) J K (K.over (G.obj X))
  letI := Functor.isContinuous_comp (Over.star X) (Over.post G) J (J.over X)
    (K.over (G.obj X))
  let i := i₁ ≪≫ (Functor.sheafPushforwardContinuousIso (starPostIso G X).symm
    (ModuleCat.{w} R) J (K.over (G.obj X))) ≪≫ i₂.symm
  exact ((conjugateIsoEquiv adj₁ adj₂).symm i).symm

private def constantRestrictionIso {X Y : D} (f : X ⟶ Y) (M : ModuleCat.{w} R) :
    (K.overMapPullback (ModuleCat.{w} R) f).obj
        ((constantSheaf (K.over Y) (ModuleCat.{w} R)).obj M) ≅
      (constantSheaf (K.over X) (ModuleCat.{w} R)).obj M :=
  ((Over.map f).pushforwardContinuousSheafificationCompatibility
    (ModuleCat.{w} R) (K.over X) (K.over Y)).symm.app
      ((Functor.const (Over Y)ᵒᵖ).obj M)

/-- A finite module local system stays such under inverse image along a continuous
finite-limit-preserving functor of small sites.
Source: Stacks Project, Sites, Tags 00YV and 00XZ. -/
theorem coefficient_finite_local_systems_pullback
    (F : Sheaf J (ModuleCat.{w} R))
    (hF : IsCoefficientModelLocallyConstantFinite J R F) :
    IsCoefficientModelLocallyConstantFinite K R
      ((Functor.sheafPullbackConstruction.sheafPullback G (ModuleCat.{w} R) J K).obj F) := by
  intro V
  let T : C := ⊤_ C
  obtain ⟨S, hS, hmodels⟩ := hF T
  let t : IsTerminal (G.obj T) := (terminalIsTerminal (C := C)).isTerminalObj G
  let a := t.from V
  refine ⟨(S.functorPushforward G).pullback a,
    K.pullback_stable a ((CoverPreserving.of_isContinuous G J K).cover_preserve hS), ?_⟩
  intro W f hf
  obtain ⟨Y, g, q, hg, _⟩ := hf
  obtain ⟨M, hM, ⟨e⟩⟩ := hmodels Y g hg
  let H : Over Y ⥤ Over (G.obj Y) := Over.post G
  let h₁ : IsTerminal (H.obj (Over.mk (𝟙 Y))) := by
    change IsTerminal (Over.mk (G.map (𝟙 Y)))
    rw [G.map_id]
    exact Over.mkIdTerminal
  let e₁ := (pullbackOverIso J K G R Y).app F
  let e₂ := (Functor.sheafPullbackConstruction.sheafPullback H
    (ModuleCat.{w} R) (J.over Y) (K.over (G.obj Y))).mapIso e
  let e₃ :=
    ((Functor.sheafPullbackConstruction.sheafPullbackIso H
      (ModuleCat.{w} R) (J.over Y) (K.over (G.obj Y))).symm.app
        ((constantSheaf (J.over Y) (ModuleCat.{w} R)).obj M)) ≪≫
      (H.constantSheafsheafPullbackIso (ModuleCat.{w} R) (J.over Y) (K.over (G.obj Y))
        (Over.mkIdTerminal (X := Y)) h₁).app M
  let e₄ := (K.overMapPullback (ModuleCat.{w} R) q).mapIso (e₁ ≪≫ e₂ ≪≫ e₃)
  exact ⟨M, hM, ⟨(Sheaf.pushforwardOverMapIso _ q).symm ≪≫ e₄ ≪≫
    constantRestrictionIso K R q M⟩⟩

end CategoryTheory
