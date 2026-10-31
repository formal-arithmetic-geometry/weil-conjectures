/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Reindex.AdicReindexScalarData
public import WeilConjectures.SixFunctors.AdicQbarRealization.Integral.AdicRealizationIntegralReindex

/-! # Construction of the source realization comparison

Source: Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15.
(blueprint: def-sf-adic-reindex-source-construction)
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

section Composite
variable {A B C D E F : Type*}
  [Category A] [Category B] [Category C] [Category D] [Category E] [Category F]
  (P : A ⥤ B) (W : B ⥤ D) (V : A ⥤ E) (J : B ⥤ C) (U : A ⥤ C)
  (R : C ⥤ F) (TX : D ⥤ F) (G : E ⥤ D)
  (e : U = P ⋙ J) (r : J ⋙ R ≅ W ⋙ TX) (p : V ⋙ G ≅ P ⋙ W)

/-- Source factors of an integral reindexing comparison in arbitrary categories. -/
@[irreducible] def realizationReindexSourceComposite : U ⋙ R ≅ V ⋙ G ⋙ TX :=
  Functor.isoWhiskerRight (eqToIso e) R ≪≫
    Functor.associator P J R ≪≫
    Functor.isoWhiskerLeft P r ≪≫ (Functor.associator P W TX).symm ≪≫
    Functor.isoWhiskerRight p.symm TX ≪≫ Functor.associator V G TX

/-- Component calculation before specializing to any derived categories. -/
theorem realizationReindexSourceComposite_hom (K : A) :
    (realizationReindexSourceComposite P W V J U R TX G e r p).hom.app K =
      R.map (eqToHom (Functor.congr_obj e K)) ≫ r.hom.app (P.obj K) ≫
        TX.map (p.inv.app K) := by
  delta realizationReindexSourceComposite
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Iso.symm_hom,
    eqToIso.hom, eqToHom_app, Category.id_comp, Category.comp_id]
/-- Factor the integral composite before introducing concrete coefficient categories. -/
theorem realizationReindexComposite_source {N : Type*} [Category N]
    (TY : E ⥤ N) (F' : N ⥤ F) (Z : A ⥤ N)
    (i : TY ⋙ F' ≅ G ⋙ TX) (s : Z ≅ V ⋙ TY) (K : A) :
    (realizationReindexComposite P W V J U R TX TY G F' Z e r p i s).hom.app K =
      (realizationReindexSourceComposite P W V J U R TX G e r p).hom.app K ≫
        i.inv.app (V.obj K) ≫ F'.map (s.inv.app K) := by
  rw [realizationReindexComposite_hom, realizationReindexSourceComposite_hom]
  simp only [Category.assoc]
end Composite

/-- The literal stage object equals localization of the completed integral extension. -/
theorem realizationStageObject_eq (l : ℕ) [Fact l.Prime] (W : Scheme.{u})
    (E L : Index l (PadicAlgCl l)) (h : E ≤ L)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) W) :
    (((inclusion (l := l) (Ω := PadicAlgCl l) (Y := W) E).obj
      ((sfRationalConstructibleLocalization l
        (Coefficient.{u} l (PadicAlgCl l) E) W).obj K)).toStage h) =
      (sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) L) W).obj
        ((integralTransition l (PadicAlgCl l) W E L h).obj K) := by
  change ((stageSystem l (PadicAlgCl l) W).T h).obj _ = _
  rw [(GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique l
    (PadicAlgCl l) W).exists.choose_spec.1 E L h]
  exact (sfRationalScalarExtension_existsUnique l (Coefficient.{u} l (PadicAlgCl l) E)
    W 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l (PadicAlgCl l) L)
    (coefficientInclusion l (PadicAlgCl l) E L h)).exists.choose_spec.2.1 _

/-- Coefficient enlargement ending at the specified integral representative. -/
def realizationScalarArrow (l : ℕ) [Fact l.Prime] (W : Scheme.{u})
    (E L : Index l (PadicAlgCl l)) (h : E ≤ L)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) W) :
    (inclusion (l := l) (Ω := PadicAlgCl l) (Y := W) E).obj
        ((sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) W).obj K) ⟶
      (inclusion (l := l) (Ω := PadicAlgCl l) (Y := W) L).obj
        ((sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) L) W).obj
          ((integralTransition l (PadicAlgCl l) W E L h).obj K)) :=
  ((stageSystem l (PadicAlgCl l) W).isoToStage
    ((inclusion (l := l) (Ω := PadicAlgCl l) (Y := W) E).obj
      ((sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) W).obj K))
    h).hom ≫
    (inclusion (l := l) (Ω := PadicAlgCl l) (Y := W) L).map
      (eqToHom (realizationStageObject_eq l W E L h K))

section SourceDefinition
attribute [local irreducible] StageSystem.ι

/-- Construct the source half: source transport, realization, then inverse completion.
No target realization or balanced reindexing datum enters this construction. -/
@[irreducible] def realizationReindexSource (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (R : LocallyFiniteAdicRealization.Realization l X) (E : Index l (PadicAlgCl l)) :
    sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) Y ⋙
        inclusion (l := l) (Ω := PadicAlgCl l) (Y := Y) E ⋙
          commonStageDerivedPullback l (PadicAlgCl l) g ⋙ ordinary l X R ≅
      (sfIntegralConstructible l (Coefficient.{u} l (PadicAlgCl l) E) Y).ι ⋙
        podCompletedDerivedInverseImage l (Coefficient.{u} l (PadicAlgCl l) E) g ⋙
          pbcDerivedExtend (coefficientMap l X R E) := by
  let QX := sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) X
  let QY := sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) Y
  let IX := inclusion (l := l) (Ω := PadicAlgCl l) (Y := X) E
  let P := constructibleIntegralPullback l (Coefficient.{u} l (PadicAlgCl l) E) g
  let W := (sfIntegralConstructible l (Coefficient.{u} l (PadicAlgCl l) E) X).ι
  let V := (sfIntegralConstructible l (Coefficient.{u} l (PadicAlgCl l) E) Y).ι
  let TX := pbcDerivedExtend (coefficientMap l X R E)
  let G := podCompletedDerivedInverseImage l (Coefficient.{u} l (PadicAlgCl l) E) g
  let e := (congrArg (fun Z ↦ QY ⋙ Z) (realizationPullback_inclusion_eq l g E)).trans
    (congrArg (fun Z ↦ Z ⋙ IX) (realizationPullback_localization_eq l g E))
  let r : (QX ⋙ IX) ⋙ ordinary l X R ≅ W ⋙ TX := R.integral E
  exact realizationReindexSourceComposite P W V (QX ⋙ IX)
    (QY ⋙ inclusion (l := l) (Ω := PadicAlgCl l) (Y := Y) E ⋙
      commonStageDerivedPullback l (PadicAlgCl l) g) (ordinary l X R) TX G e r
    (realizationCompletionPullbackIso l g E)

end SourceDefinition

end WeilConjectures.AdicQbarRealization
