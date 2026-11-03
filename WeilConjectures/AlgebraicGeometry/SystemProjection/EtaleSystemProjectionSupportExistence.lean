/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SystemProjection.EtaleSystemProjectionData
import all WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations
import WeilConjectures.SixFunctors.SequenceModuleEvaluation.SequenceModulePullbackEvaluation
import all WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownLevelRealizationData
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ConstantSheaf
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

/-! # Support operations for normalized etale systems

Source: Zheng, Constructions 4.1 and 5.14--5.15; Stacks Tag 0GL6
(blueprint: lem-pur-etale-system-projection-support-existence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale.SystemProjection

open WeilConjectures WeilConjectures.SemilinearSections
open AlgebraicGeometry.ProEtale.VaryingRing
open CategoryTheory.Functor

attribute [local irreducible] Functor.leftAdjoint

private abbrev baseSite {X Y : Scheme.{u}} (g : X ⟶ Y) : Y.Etale ⥤ X.Etale :=
  MorphismProperty.Over.pullback @Etale ⊤ g

private instance baseContinuous {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (MorphismProperty.Over.pullback @Etale ⊤ g).IsContinuous
      Y.smallEtaleTopology X.smallEtaleTopology :=
  AlgebraicGeometry.Etale.isContinuous_overPullback g

private instance siteContinuous {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (siteMap g).IsContinuous (coefficientSequenceTopology Y.smallEtaleTopology)
      (coefficientSequenceTopology X.smallEtaleTopology) :=
  prodContinuous _ _ _

private def constantDirect {X Y : Scheme.{u}} (g : X ⟶ Y)
    (A : CommRingCat.{u + 1}) :
    (constantSheaf Y.smallEtaleTopology CommRingCat.{u + 1}).obj A ⟶
      ((MorphismProperty.Over.pullback @Etale ⊤ g).sheafPushforwardContinuous
        CommRingCat.{u + 1} Y.smallEtaleTopology X.smallEtaleTopology).obj
        ((constantSheaf X.smallEtaleTopology CommRingCat.{u + 1}).obj A) :=
  ((sheafificationAdjunction Y.smallEtaleTopology CommRingCat.{u + 1}).homEquiv _ _).symm
    (Functor.whiskerLeft (MorphismProperty.Over.pullback @Etale ⊤ g).op
      (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj A)))

private theorem constantDirect_unit {X Y : Scheme.{u}} (g : X ⟶ Y)
    (A : CommRingCat.{u + 1}) (U : Y.Etaleᵒᵖ) :
    (toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj A)).app U ≫
      (constantDirect g A).hom.app U =
        (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj A)).app
          ((MorphismProperty.Over.pullback @Etale ⊤ g).op.obj U) := by
  have h := ((sheafificationAdjunction Y.smallEtaleTopology CommRingCat.{u + 1}).homEquiv
    ((Functor.const Y.Etaleᵒᵖ).obj A)
    (((MorphismProperty.Over.pullback @Etale ⊤ g).sheafPushforwardContinuous
      CommRingCat.{u + 1} Y.smallEtaleTopology X.smallEtaleTopology).obj
      ((constantSheaf X.smallEtaleTopology CommRingCat.{u + 1}).obj A))).apply_symm_apply
      (Functor.whiskerLeft (MorphismProperty.Over.pullback @Etale ⊤ g).op
        (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj A)))
  exact congrArg (fun k ↦ k.app U) h

private theorem constantDirect_naturality {X Y : Scheme.{u}} (g : X ⟶ Y)
    {A D : CommRingCat.{u + 1}} (a : A ⟶ D) :
    (constantSheaf Y.smallEtaleTopology CommRingCat.{u + 1}).map a ≫ constantDirect g D =
      constantDirect g A ≫
        ((MorphismProperty.Over.pullback @Etale ⊤ g).sheafPushforwardContinuous
          CommRingCat.{u + 1} Y.smallEtaleTopology X.smallEtaleTopology).map
          ((constantSheaf X.smallEtaleTopology CommRingCat.{u + 1}).map a) := by
  apply ((sheafificationAdjunction Y.smallEtaleTopology CommRingCat.{u + 1}).homEquiv
    ((Functor.const Y.Etaleᵒᵖ).obj A) _).injective
  change ((sheafificationAdjunction Y.smallEtaleTopology CommRingCat.{u + 1}).homEquiv
    _ _) ((presheafToSheaf Y.smallEtaleTopology CommRingCat.{u + 1}).map
      ((Functor.const Y.Etaleᵒᵖ).map a) ≫ _) = _
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  simp only [constantDirect, Equiv.apply_symm_apply]
  apply NatTrans.ext
  funext U
  exact congrArg
    (fun t ↦ t.app ((MorphismProperty.Over.pullback @Etale ⊤ g).op.obj U))
    ((toSheafification X.smallEtaleTopology CommRingCat.{u + 1}).naturality
      ((Functor.const X.Etaleᵒᵖ).map a))

private def direct {X Y : Scheme.{u}} (g : X ⟶ Y)
    (B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) : DirectImage g B := by
  let δ : SemilinearSections.rings Y.smallEtaleTopology (coefficients Y B)
      (transitions Y B) ⟶
      SemilinearSections.rings X.smallEtaleTopology (coefficients X B)
        (transitions X B) ⋙
        (MorphismProperty.Over.pullback @Etale ⊤ g).sheafPushforwardContinuous
          CommRingCat.{u + 1} Y.smallEtaleTopology X.smallEtaleTopology :=
    NatTrans.ofOpSequence (fun n ↦ constantDirect g (B.obj (op n))) (by
      intro n
      dsimp only [SemilinearSections.rings, Functor.comp_map]
      simp only [Functor.ofOpSequence_map_homOfLE_succ]
      exact constantDirect_naturality g (B.map (homOfLE (Nat.le_succ n)).op))
  let ε := Functor.whiskerLeft (prodOpEquiv (C := ℕ) (D := Y.Etale)).functor
    (Functor.uncurry.map
      (Functor.whiskerRight δ (sheafToPresheaf Y.smallEtaleTopology
        CommRingCat.{u + 1})))
  exact {
    continuous := inferInstance
    structural := ⟨ε⟩
    constants := fun n U b ↦ ConcreteCategory.congr_hom (constantDirect_unit g _ U) b
  }

private abbrev singleRing (W : Scheme.{u}) (A : CommRingCat.{u + 1}) :=
  SemilinearSections.ring W.smallEtaleTopology
    ((constantSheaf W.smallEtaleTopology CommRingCat.{u + 1}).obj A)

private def singleMap {X Y : Scheme.{u}} (g : X ⟶ Y) (A : CommRingCat.{u + 1}) :=
  (sheafCompose Y.smallEtaleTopology (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
    (constantDirect g A)

private abbrev singlePush {X Y : Scheme.{u}} (g : X ⟶ Y)
    (A : CommRingCat.{u + 1}) :
    SheafOfModules.{u + 1} (singleRing X A) ⥤
      SheafOfModules.{u + 1} (singleRing Y A) :=
  SheafOfModules.pushforward.{u + 1}
    (F := MorphismProperty.Over.pullback @Etale ⊤ g)
    (R := singleRing X A) (S := singleRing Y A) (singleMap g A)

private abbrev singlePull {X Y : Scheme.{u}} (g : X ⟶ Y)
    (A : CommRingCat.{u + 1}) :
    SheafOfModules.{u + 1} (singleRing Y A) ⥤
      SheafOfModules.{u + 1} (singleRing X A) := (singlePush g A).leftAdjoint

private def singleAdj {X Y : Scheme.{u}} (g : X ⟶ Y) (A : CommRingCat.{u + 1}) :
    singlePull g A ⊣ singlePush g A := Adjunction.ofIsRightAdjoint _

private instance sliceContinuous (W : Scheme.{u}) (n : ℕ) :
    (Prod.sectR n W.Etale).IsContinuous W.smallEtaleTopology
      (coefficientSequenceTopology W.smallEtaleTopology) :=
  SemilinearSections.evaluationContinuous.{u + 1, u, u + 1} _ _

private abbrev ev (W : Scheme.{u}) (B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) (n : ℕ) :=
  SemilinearSections.evaluation.{u + 1, u, u + 1}
    W.smallEtaleTopology (coefficients W B) (transitions W B) n

private abbrev sequenceRing (W : Scheme.{u}) (B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) :=
  SemilinearSections.ring (coefficientSequenceTopology W.smallEtaleTopology) (rings W B)

private instance pushAdd {X Y : Scheme.{u}} (g : X ⟶ Y)
    (B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) : ((direct g B).push).Additive := by
  constructor
  intro M N a b
  ext U x
  rfl

private abbrev pull {X Y : Scheme.{u}} (g : X ⟶ Y)
    (B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) : Modules Y B ⥤ Modules X B :=
  (direct g B).push.leftAdjoint

private def pullAdj {X Y : Scheme.{u}} (g : X ⟶ Y)
    (B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) : pull g B ⊣ (direct g B).push :=
  Adjunction.ofIsRightAdjoint _

private def pushEvaluation {X Y : Scheme.{u}} (g : X ⟶ Y)
    (B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) (n : ℕ) :
    (direct g B).push ⋙ ev Y B n ≅ ev X B n ⋙ singlePush g (B.obj (op n)) :=
  (@towerPushforwardEvaluation.{u} Y.Etale X.Etale _ _ _ _
    Y.smallEtaleTopology X.smallEtaleTopology
    (MorphismProperty.Over.pullback @Etale ⊤ g) (baseContinuous g) (siteContinuous g)
    (coefficients Y B) (transitions Y B) (coefficients X B) (transitions X B) n
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (direct g B).structural) (singleMap g (B.obj (op n))) (by intro U; rfl)).choose

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option maxHeartbeats 2000000 in
-- Elaborating the transported adjunction unfolds the coefficient and evaluation functors.
private def pullEvaluation {X Y : Scheme.{u}} (g : X ⟶ Y)
    (B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) (n : ℕ) :
    pull g B ⋙ ev X B n ≅ ev Y B n ⋙ singlePull g (B.obj (op n)) := by
  have h :=
    @SequenceModuleEvaluation.sequenceModulePullbackEvaluation_isIso
      Y.Etale _ _ _ _ X.Etale _ _ _ _
      Y.smallEtaleTopology X.smallEtaleTopology (baseSite g)
      (baseContinuous g) (siteContinuous g) (sequenceRing Y B) (sequenceRing X B) n
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (direct g B).structural) (singleRing Y (B.obj (op n)))
      (singleRing X (B.obj (op n)))
      (evaluation_ring.{u + 1, u, u + 1} Y.smallEtaleTopology
        (coefficients Y B) (transitions Y B) n)
      (evaluation_ring.{u + 1, u, u + 1} X.smallEtaleTopology
        (coefficients X B) (transitions X B) n)
      (singleMap g (B.obj (op n))) (pull g B) (singlePull g (B.obj (op n))) (pullAdj g B)
      (singleAdj g (B.obj (op n))) (pushEvaluation g B n)
  let α : ev Y B n ⋙ singlePull g (B.obj (op n)) ⟶ pull g B ⋙ ev X B n :=
    ((mateEquiv (G := ev Y B n) (H := ev X B n)
      (pullAdj g B) (singleAdj g (B.obj (op n)))).symm (pushEvaluation g B n).hom).natTrans
  letI : IsIso α := h
  exact (asIso α).symm

private theorem pullExact {X Y : Scheme.{u}} (g : X ⟶ Y)
    (B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) :
    PreservesFiniteLimits (pull g B) ∧ PreservesFiniteColimits (pull g B) := by
  obtain ⟨A⟩ := semilinearDerivedSections.{u + 1, u, u + 1}
    X.smallEtaleTopology (coefficients X B) (transitions X B)
  exact exact_of_componentwise (A := Modules Y B) (B := Modules X B)
    (C := fun n ↦ SheafOfModules.{u + 1} (singleRing Y (B.obj (op n))))
    (D := fun n ↦ SheafOfModules.{u + 1} (singleRing X (B.obj (op n))))
    (pull g B) (ev X B) (ev Y B) (fun n ↦ singlePull g (B.obj (op n)))
    A.systems.componentwise (pullEvaluation g B)

private theorem modulesKinjective (W : Scheme.{u}) (B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) :
    Abelian.HasKInjectiveResolutions (Modules W B) := by
  let := (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{
    u + 1, u, u + 1} (coefficientSequenceTopology W.smallEtaleTopology)
      (rings W B)).1
  infer_instance

private def image {X Y : Scheme.{u}} (g : X ⟶ Y)
    (B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) : Image g B where
  toDirectImage := direct g B
  inverse := pull g B
  adjunction := pullAdj g B
  inverseAdditive := inferInstance
  inverseLimits := (pullExact g B).1
  inverseColimits := (pullExact g B).2
  pushAdditive := inferInstance
  kinjectives := modulesKinjective X B

private abbrev openSite {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    U.Etale ⥤ X.Etale :=
  MorphismProperty.Over.map ⊤ (inferInstance : Etale j)

private instance openSiteContinuous {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : (openSite j).IsContinuous U.smallEtaleTopology
      X.smallEtaleTopology :=
  Scheme.isContinuous_overMap (inferInstance : Etale j) le_rfl

private def openSiteAdj {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    openSite j ⊣ MorphismProperty.Over.pullback @Etale ⊤ j :=
  MorphismProperty.Over.mapPullbackAdj @Etale ⊤ j inferInstance trivial

private instance openSequenceContinuous {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : ((𝟭 ℕ).prod (openSite j)).IsContinuous
      (coefficientSequenceTopology U.smallEtaleTopology)
      (coefficientSequenceTopology X.smallEtaleTopology) :=
  prodContinuous _ _ _

private def openCommAdj {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (openSite j).sheafPushforwardContinuous CommRingCat.{u + 1}
      U.smallEtaleTopology X.smallEtaleTopology ⊣
    (MorphismProperty.Over.pullback @Etale ⊤ j).sheafPushforwardContinuous CommRingCat.{u + 1}
      X.smallEtaleTopology U.smallEtaleTopology := by
  let := openSiteContinuous j
  let := baseContinuous j
  exact (openSiteAdj j).sheafPushforwardContinuous
    U.smallEtaleTopology X.smallEtaleTopology

private def openSeqAdj {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    ((𝟭 ℕ).prod (openSite j)).sheafPushforwardContinuous RingCat.{u + 1}
      (coefficientSequenceTopology U.smallEtaleTopology)
      (coefficientSequenceTopology X.smallEtaleTopology) ⊣
    (siteMap j).sheafPushforwardContinuous RingCat.{u + 1}
      (coefficientSequenceTopology X.smallEtaleTopology)
      (coefficientSequenceTopology U.smallEtaleTopology) := by
  let := openSequenceContinuous j
  let := siteContinuous j
  exact (prodAdj (openSiteAdj j)).sheafPushforwardContinuous
    (coefficientSequenceTopology U.smallEtaleTopology)
    (coefficientSequenceTopology X.smallEtaleTopology)

private def openConstantTranspose {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (A : CommRingCat.{u + 1}) :
    ((openSite j).sheafPushforwardContinuous CommRingCat.{u + 1}
      U.smallEtaleTopology X.smallEtaleTopology).obj
        ((constantSheaf X.smallEtaleTopology CommRingCat.{u + 1}).obj A) ⟶
      (constantSheaf U.smallEtaleTopology CommRingCat.{u + 1}).obj A :=
  ((openCommAdj j).homEquiv _ _).symm (constantDirect j A)

private def openLevelTranspose {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (A : CommRingCat.{u + 1}) :
    ((openSite j).sheafPushforwardContinuous RingCat.{u + 1}
      U.smallEtaleTopology X.smallEtaleTopology).obj (singleRing X A) ⟶
        singleRing U A :=
  ⟨Functor.whiskerRight (openConstantTranspose j A).hom
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩

private def openLevelPull {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (A : CommRingCat.{u + 1}) :
    SheafOfModules.{u + 1} (singleRing X A) ⥤ SheafOfModules.{u + 1} (singleRing U A) :=
  SheafOfModules.pushforward (F := openSite j) (inv (openLevelTranspose j A))

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option maxHeartbeats 2000000 in
-- Elaborating the transported adjunction unfolds the coefficient and evaluation functors.
private def openRingTranspose {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) :
    (((𝟭 ℕ).prod (openSite j)).sheafPushforwardContinuous RingCat.{u + 1}
      (coefficientSequenceTopology U.smallEtaleTopology)
      (coefficientSequenceTopology X.smallEtaleTopology)).obj (sequenceRing X B) ⟶
        sequenceRing U B :=
  ((openSeqAdj j).homEquiv _ _).symm
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (direct j B).structural)

private theorem openRingTranspose_app {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) (V : (ℕ × U.Etale)ᵒᵖ) :
    (openRingTranspose j B).hom.app V =
      (openLevelTranspose j (B.obj (op V.unop.1))).hom.app (op V.unop.2) := by
  simp only [openRingTranspose, openLevelTranspose, openConstantTranspose,
    openSeqAdj, openCommAdj, Adjunction.homEquiv_counit]
  change _ = (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
    ((constantDirect j (B.obj (op V.unop.1))).hom.app (op ((openSite j).obj V.unop.2)) ≫
      (coefficients U B V.unop.1).obj.map ((openSiteAdj j).unit.app V.unop.2).op)
  change (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
    ((constantDirect j (B.obj (op V.unop.1))).hom.app (op ((openSite j).obj V.unop.2)) ≫
      ((SemilinearSections.rings U.smallEtaleTopology (coefficients U B)
        (transitions U B)).map (𝟙 (op V.unop.1))).hom.app
          (op ((MorphismProperty.Over.pullback @Etale ⊤ j).obj
            ((openSite j).obj V.unop.2))) ≫
        (coefficients U B V.unop.1).obj.map ((openSiteAdj j).unit.app V.unop.2).op) = _
  rw [CategoryTheory.Functor.map_id]
  rfl

private instance openRingTransposeIso {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) :
    IsIso (openRingTranspose j B) := by
  have h (V : (ℕ × U.Etale)ᵒᵖ) : IsIso ((openRingTranspose j B).hom.app V) := by
    rw [openRingTranspose_app]
    infer_instance
  have : IsIso ((sheafToPresheaf _ RingCat.{u + 1}).map (openRingTranspose j B)) :=
    (NatTrans.isIso_iff_isIso_app _).mpr h
  exact isIso_of_reflects_iso _ (sheafToPresheaf _ RingCat.{u + 1})

private def openPull {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) : Modules X B ⥤ Modules U B :=
  SheafOfModules.pushforward (F := (𝟭 ℕ).prod (openSite j)) (inv (openRingTranspose j B))

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option maxHeartbeats 2000000 in
-- Elaborating the transported adjunction unfolds the coefficient and evaluation functors.
private def openPullAdj {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) :
    openPull j B ⊣ (direct j B).push :=
  @moduleAdjOfSiteAdj.{u} (ℕ × U.Etale) (ℕ × X.Etale) _ _
    ((𝟭 ℕ).prod (openSite j)) (siteMap j)
    (coefficientSequenceTopology U.smallEtaleTopology)
    (coefficientSequenceTopology X.smallEtaleTopology)
    (openSequenceContinuous j) (siteContinuous j) (prodAdj (openSiteAdj j))
    (sequenceRing U B) (sequenceRing X B)
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (direct j B).structural) (openRingTransposeIso j B)

private abbrev levelExtension {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (A : CommRingCat.{u + 1}) :
    SheafOfModules.{u + 1} (singleRing U A) ⥤ SheafOfModules.{u + 1} (singleRing X A) :=
  (openLevelPull j A).leftAdjoint

private def levelExtensionAdj {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (A : CommRingCat.{u + 1}) :
    levelExtension j A ⊣ openLevelPull j A := Adjunction.ofIsRightAdjoint _

private theorem openPullExact {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) :
    PreservesFiniteLimits (openPull j B) ∧ PreservesFiniteColimits (openPull j B) := by
  let := (pullExact j B).1
  let := (pullExact j B).2
  let e := (pullAdj j B).leftAdjointUniq (openPullAdj j B)
  exact ⟨preservesFiniteLimits_of_natIso e, preservesFiniteColimits_of_natIso e⟩

private abbrev openExtension {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) : Modules U B ⥤ Modules X B :=
  (openPull j B).leftAdjoint

private def openExtensionAdj {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) :
    openExtension j B ⊣ openPull j B := Adjunction.ofIsRightAdjoint _

private theorem openTranspose_inv_app {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) (n : ℕ) (V : U.Etaleᵒᵖ) :
    (inv (openRingTranspose j B)).hom.app (op (n, V.unop)) =
      (inv (openLevelTranspose j (B.obj (op n)))).hom.app V := by
  simp only [ObjectProperty.hom_inv, NatIso.isIso_inv_app, openRingTranspose_app]

private def openPullEvaluation {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) (n : ℕ) :
    openPull j B ⋙ ev U B n ≅ ev X B n ⋙ openLevelPull j (B.obj (op n)) :=
  (@towerPushforwardEvaluation.{u} U.Etale X.Etale _ _ _ _
    U.smallEtaleTopology X.smallEtaleTopology (openSite j)
    (openSiteContinuous j) (openSequenceContinuous j)
    (coefficients U B) (transitions U B) (coefficients X B) (transitions X B) n
    (inv (openRingTranspose j B)) (inv (openLevelTranspose j (B.obj (op n))))
    (openTranspose_inv_app j B n)).choose

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option maxHeartbeats 2000000 in
-- Elaborating the transported adjunction unfolds the coefficient and evaluation functors.
private def openExtensionEvaluation {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) (n : ℕ) :
    openExtension j B ⋙ ev X B n ≅ ev U B n ⋙ levelExtension j (B.obj (op n)) := by
  have h :=
    @SequenceModuleEvaluation.sequenceModulePullbackEvaluation_isIso
      U.Etale _ _ _ _ X.Etale _ _ _ _
      U.smallEtaleTopology X.smallEtaleTopology (openSite j)
      (openSiteContinuous j) (openSequenceContinuous j) (sequenceRing U B) (sequenceRing X B) n
      (inv (openRingTranspose j B)) (singleRing U (B.obj (op n)))
      (singleRing X (B.obj (op n)))
      (evaluation_ring.{u + 1, u, u + 1} U.smallEtaleTopology
        (coefficients U B) (transitions U B) n)
      (evaluation_ring.{u + 1, u, u + 1} X.smallEtaleTopology
        (coefficients X B) (transitions X B) n)
      (inv (openLevelTranspose j (B.obj (op n))))
      (openExtension j B) (levelExtension j (B.obj (op n))) (openExtensionAdj j B)
      (levelExtensionAdj j (B.obj (op n))) (openPullEvaluation j B n)
  let α : ev U B n ⋙ levelExtension j (B.obj (op n)) ⟶ openExtension j B ⋙ ev X B n :=
    ((mateEquiv (G := ev U B n) (H := ev X B n)
      (openExtensionAdj j B) (levelExtensionAdj j (B.obj (op n)))).symm
        (openPullEvaluation j B n).hom).natTrans
  letI : IsIso α := h
  exact (asIso α).symm

private theorem openExtensionExact {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) :
    PreservesFiniteLimits (openExtension j B) ∧ PreservesFiniteColimits (openExtension j B) := by
  obtain ⟨A⟩ := semilinearDerivedSections.{u + 1, u, u + 1}
    X.smallEtaleTopology (coefficients X B) (transitions X B)
  exact exact_of_componentwise (A := Modules U B) (B := Modules X B)
    (C := fun n ↦ SheafOfModules.{u + 1} (singleRing U (B.obj (op n))))
    (D := fun n ↦ SheafOfModules.{u + 1} (singleRing X (B.obj (op n))))
    (openExtension j B) (ev X B) (ev U B) (fun n ↦ levelExtension j (B.obj (op n)))
    A.systems.componentwise (openExtensionEvaluation j B)

private def openImage {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) : OpenImage j B where
  toDirectImage := direct j B
  inverse := openPull j B
  adjunction := openPullAdj j B
  inverseAdditive := inferInstance
  inverseLimits := (openPullExact j B).1
  inverseColimits := (openPullExact j B).2
  pushAdditive := inferInstance
  kinjectives := modulesKinjective U B
  targetKinjectives := modulesKinjective X B
  extension := openExtension j B
  openAdjunction := openExtensionAdj j B
  extensionAdditive := inferInstance
  extensionLimits := (openExtensionExact j B).1
  extensionColimits := (openExtensionExact j B).2

end AlgebraicGeometry.Etale.SystemProjection
