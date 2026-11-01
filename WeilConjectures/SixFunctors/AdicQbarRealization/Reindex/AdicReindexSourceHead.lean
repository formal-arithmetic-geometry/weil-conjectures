/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Reindex.AdicReindexSourceConstruction
import WeilConjectures.SixFunctors.AdicQbarRealization.ScalarSourceCalculus.AdicReindexSourceCalculus

/-! # The scalar-arrow head of the source comparison

Source: Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15.
(blueprint: lem-sf-adic-reindex-source-head)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option cleanup.letToHave false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization
attribute [local irreducible] HasDerivedCategory.standard
  derivedPull LocallyFiniteAdicRealization.sections
  LocallyFiniteAdicRealization.CoefficientPresentation.integralMap
  podCompletedDerivedInverseImage integralDerivedPullback
  commonStageDerivedPullback rationalDerivedPullback

open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open GeneralAlgebraicallyClosedCoefficients (inclusion stageSystem integralTransition)

open ScalarSourceCalculus

attribute [local implicit_reducible] StageSystem.ι
  GeneralAlgebraicallyClosedCoefficients.Stage
  GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.pairCategory
  integralScalarExtensionOfUniverses

-- Keep the selected comparison maps abstract while checking the final square.
attribute [local irreducible] completedScalarReindex completedReindexModel scalarExactModel
  integralPullbackScalarComparison podCompletedToTowerIso pbcReductionNormalization
  pbcReductionNormalizationHom pbcReductionTransition
  podCompletedToTower pbcDerivedScalarAdjunction
attribute [local implicit_reducible] ordinary coefficientMap
  LocallyFiniteAdicRealization.ringSheaf AlgebraicGeometry.Scheme.residueField

private theorem head_transition_paste
    {C D V : Type*} [Category C] [Category D] [Category V]
    (O : C ⥤ D) (N : V ⥤ D)
    {A A' B B' M : C} {P Q : V} {U : D}
    (eA : A = A') (eB : B = B') (f : A ⟶ B) (x : A' ⟶ M) (b : M ⟶ B')
    (rA : O.obj A' ⟶ U) (rM : O.obj M ≅ N.obj P) (rB : O.obj B' ⟶ N.obj Q)
    (t : U ⟶ N.obj P) (δ : P ⟶ Q)
    (hp : f ≫ eqToHom eB = eqToHom eA ≫ x ≫ b)
    (hn : O.map b ≫ rB = rM.hom ≫ N.map δ)
    (ho : O.map x = rA ≫ t ≫ rM.inv) :
    O.map f ≫ (O.map (eqToHom eB) ≫ rB) =
      (O.map (eqToHom eA) ≫ rA) ≫ t ≫ N.map δ := by
  have hm := congrArg O.map hp
  simp only [O.map_comp] at hm
  rw [← Category.assoc, hm]
  simp only [Category.assoc]
  rw [hn, ho]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- Realization of the pulled-back coefficient arrow, before completion cancellation.
Source: BS Remark 6.8.15 and Proposition 6.8.14.
(blueprint: lem-sf-adic-reindex-source-head).

Proof: the normalized common-stage arrow formula supplies the transported square.
Apply ordinary realization, substitute R.common_field, and use naturality of
R.integral(L). Its inverse components cancel, retaining the native scalar transition
as a single map. -/
theorem source_scalar_head (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (R : LocallyFiniteAdicRealization.Realization l X)
    (E L : Index l (PadicAlgCl l)) (h : E ≤ L)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) Y) :
    let C := Coefficient.{u} l (PadicAlgCl l)
    let i := coefficientInclusion l (PadicAlgCl l) E L h
    let P (F : Index l (PadicAlgCl l)) := constructibleIntegralPullback l (C F) g
    let Q (W : Scheme.{u}) (F : Index l (PadicAlgCl l)) :=
      sfRationalConstructibleLocalization l (C F) W
    let I (W : Scheme.{u}) (F : Index l (PadicAlgCl l)) :=
      inclusion (l := l) (Ω := PadicAlgCl l) (Y := W) F
    let F := commonStageDerivedPullback l (PadicAlgCl l) g
    let O := ordinary l X R
    let NL := pbcDerivedExtend (coefficientMap l X R L)
    let KL := (integralTransition l (PadicAlgCl l) Y E L h).obj K
    let KE := (P E).obj K
    let δ := (integralPullbackScalarComparison l (C E) (C L) i g K).hom
    let e (J : Index l (PadicAlgCl l)) :=
      (congrArg (fun Z ↦ Q Y J ⋙ Z) (realizationPullback_inclusion_eq l g J)).trans
        (congrArg (fun Z ↦ Z ⋙ I X J) (realizationPullback_localization_eq l g J))
    let r := O.map (eqToHom (Functor.congr_obj (e E) K)) ≫ (R.integral E).hom.app KE
    let s := O.map (eqToHom (Functor.congr_obj (e L) KL)) ≫
      (R.integral L).hom.app ((P L).obj KL)
    (F ⋙ O).map (realizationScalarArrow l Y E L h K) ≫ s =
      r ≫ nativeScalarTransition l X R E L h KE.obj ≫ NL.map δ.hom := by
  intro C i P Q I F O NL KL KE δ e r s
  let aY := realizationScalarArrow l Y E L h K
  let aX := realizationScalarArrow l X E L h KE
  let b := (I X L).map ((Q X L).map δ)
  have hp := transport_square (F.map aY) (aX ≫ b)
    (Functor.congr_obj (e E) K) (Functor.congr_obj (e L) KL)
    (pullback_scalar_arrow l g E L h K)
  have hn := (R.integral L).hom.naturality δ
  dsimp only [Functor.comp_map, ObjectProperty.ι_map] at hn
  have ho := ordinary_scalar_arrow l X R E L h KE
  exact head_transition_paste O NL (Functor.congr_obj (e E) K) (Functor.congr_obj (e L) KL)
    (F.map aY) aX b ((R.integral E).hom.app KE)
    ((R.integral L).app ((integralTransition l (PadicAlgCl l) X E L h).obj KE))
    ((R.integral L).hom.app ((P L).obj KL))
    (nativeScalarTransition l X R E L h KE.obj) δ.hom hp hn ho

end WeilConjectures.AdicQbarRealization
