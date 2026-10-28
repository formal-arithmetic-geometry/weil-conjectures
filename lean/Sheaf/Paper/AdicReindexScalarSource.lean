/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.AdicReindexScalarData
public import Sheaf.Paper.AdicRealizationIntegralReindex

/-! # The source half of the integral realization comparison

Source: Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15.
(blueprint: lem-sf-adic-reindex-scalar-source)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option cleanup.letToHave false

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

/-- Coefficient enlargement for the source half of the comparison.
Only R occurs: there is no target realization S, ring reindexing B, or IntegralReindex.
Source: BS Proposition 6.8.14 and Remark 6.8.15; HRS Lemma 7.9.
(blueprint: lem-sf-adic-reindex-scalar-source).

Proof in words: expand the source comparison at E and L. The normalized common-stage
pullback sends the coefficient arrow to the rational pullback scalar comparison,
conjugated by its stage identifications. Its integral representative is the prescribed
integral pullback scalar comparison. The common_field equation of R identifies the
other transition with the canonical balanced scalar associator followed by the
finite-free completion map. Naturality of that associator moves the E completion
comparison across it. The scalar square of the actual completion-unit comparison
identifies the resulting two whole-cone maps: each quotient coaugmentation has zero
shifted coordinate, and exact inverse image preserves both coordinates. Equivalently,
apply isomorphismComparison_scalarExtension after identifying podCompletedToTower
with the comparison normalized by inverse image of the actual unit. On complete
constructible inputs its two components are invertible, so cancel these components.
More explicitly, write p_E and p_L for podCompletedToTower, T for ordinary
scalar extension, χ for its completion map, and α for completed pullback/scalar
base change. The preceding normalized comparison gives
T_X(p_E) followed by χ_X followed by α =
b followed by G_L(χ_Y) followed by p_L, where b is completedScalarReindex.
Here scalarExactModel changes the exact ordinary tensor to the universal derived
tensor, and completedReindexModel changes only the equal coefficient-map presentation.
Invert p_E and p_L on these constructible inputs. Naturality of the native scalar
associator then moves native extension of p_E inverse past that associator.
Functoriality of native scalar extension gives the displayed square. Canonical equality
transports at the rational-stage endpoints compose to realizationScalarArrow. No cancellation of an
incomplete completion unit occurs. Repeated fields and empty schemes use exactly
the same normalized tensor and completion maps. -/
theorem realizationReindexSource_scalar (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (R : LocallyFiniteAdicRealization.Realization l X)
    (E L : Index l (PadicAlgCl l)) (h : E ≤ L)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) Y) :
    let i := coefficientInclusion l (PadicAlgCl l) E L h
    let C := Coefficient.{u} l (PadicAlgCl l)
    let aX := pbcReductionNormalization (completedCoefficientMap l (C E) (C L) i X)
      (coefficientMap l X R L) (coefficientMap l X R E) (R.coefficient_scalar E L h)
    (commonStageDerivedPullback l (PadicAlgCl l) g ⋙ ordinary l X R).map
        (realizationScalarArrow l Y E L h K) ≫
      (realizationReindexSource l g R L).hom.app
        ((integralTransition l (PadicAlgCl l) Y E L h).obj K) =
    (realizationReindexSource l g R E).hom.app K ≫
      (aX ((podCompletedDerivedInverseImage l (C E) g).obj K.obj)).inv ≫
      (pbcDerivedExtend (coefficientMap l X R L)).map
        ((completedScalarReindex l (C E) (C L) i g).hom.app K.obj) ≫
      (pbcDerivedExtend (coefficientMap l X R L)).map
        ((podCompletedDerivedInverseImage l (C L) g).map
          ((completedScalarComparison l (C E) (C L) i Y).app K.obj)) := by sorry

end WeilConjectures.AdicQbarRealization
