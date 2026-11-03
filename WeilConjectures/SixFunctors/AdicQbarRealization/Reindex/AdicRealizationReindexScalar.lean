/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Reindex.AdicRealizationReindexComponents
import WeilConjectures.SixFunctors.AdicQbarRealization.Reindex.AdicReindexScalarSource
import WeilConjectures.SixFunctors.AdicQbarRealization.Reindex.AdicReindexBalancedScalar

/-! # The scalar square for the prescribed integral realization components

Source: Bhatt--Scholze, Remark 6.8.15; Hemo--Richarz--Scholbach, Lemma 7.9.
(blueprint: lem-sf-adic-realization-reindex-scalar)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option cleanup.letToHave false
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.AdicQbarRealization
open AlgebraicallyClosedCoefficients (Index Coefficient)
open GeneralAlgebraicallyClosedCoefficients (stageSystem inclusion integralTransition)
open AlgebraicGeometry.Scheme
open AlgebraicallyClosedCoefficients (coefficientInclusion)

private theorem map_transport_middle
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (T : E ⥤ C) {A : C} {B B' : E} (e : B = B')
    (f : A ⟶ T.obj B) {U V W : D} (r : F.obj A ⟶ U)
    (s : U ⟶ V) (t : V ⟶ W) (v : W ⟶ F.obj (T.obj B'))
    (h : HEq (F.map f) (r ≫ s ≫ t ≫ v)) :
    F.map (f ≫ T.map (eqToHom e)) = r ≫ (s ≫ t) ≫ v := by
  cases e
  rw [eqToHom_refl, T.map_id, Category.comp_id]
  simpa only [Category.assoc] using eq_of_heq h

private theorem scalar_cube {C D : Type*} [Category C] [Category D]
    (F : D ⥤ C) {A0 A1 U V U' V' : C} {B0 B1 T0 T1 T2 : D}
    (eE : B0 ≅ T0) (eL : B1 ≅ T2)
    (f : A0 ⟶ A1) (cE : A0 ⟶ F.obj B0) (cL : A1 ⟶ F.obj B1)
    (sE : A0 ⟶ U) (sL : A1 ⟶ V) (a : U ⟶ U') (b : U' ⟶ V') (c : V' ⟶ V)
    (iE : U ⟶ F.obj T0) (iL : V ⟶ F.obj T2) (j : V' ⟶ F.obj T1)
    (v : T0 ⟶ T1) (d : T1 ⟶ T2) (h : B0 ⟶ B1)
    (hcE : cE = sE ≫ iE ≫ F.map eE.inv) (hcL : cL = sL ≫ iL ≫ F.map eL.inv)
    (hs : f ≫ sL = sE ≫ a ≫ b ≫ c)
    (hn : c ≫ iL = j ≫ F.map d) (hb : a ≫ b ≫ j = iE ≫ F.map v)
    (hy : h = eE.hom ≫ (v ≫ d) ≫ eL.inv) : f ≫ cL = cE ≫ F.map h := by
  rw [hcL, ← Category.assoc f, hs]
  simp only [Category.assoc]
  rw [reassoc_of% hn]
  rw [← Category.assoc b, ← Category.assoc a, hb]
  rw [hcE, hy]
  simp only [Functor.map_comp, Category.assoc]
  rw [← F.map_comp_assoc eE.inv eE.hom, Iso.inv_hom_id, F.map_id, Category.id_comp]

private theorem comparison_of_stage_transport
    {C D E : Type*} [Category C] [Category D] [Category E]
    (T : C ⥤ D) (A H : D ⥤ E) (c : T ⋙ A ≅ T ⋙ H)
    {P : D} {U V : C} (e : U = V) (t : P ⟶ T.obj U) (r : A.obj P ⟶ H.obj P)
    (hc : A.map (t ≫ T.map (eqToHom e)) ≫ c.hom.app V =
      r ≫ H.map (t ≫ T.map (eqToHom e))) :
    A.map t ≫ c.hom.app U = r ≫ H.map t := by
  cases e
  rw [eqToHom_refl, T.map_id, Category.comp_id] at hc
  exact hc

attribute [local irreducible] derivedPull LocallyFiniteAdicRealization.sections
  LocallyFiniteAdicRealization.CoefficientPresentation.integralMap
  podCompletedDerivedInverseImage integralDerivedPullback
  commonStageDerivedPullback rationalDerivedPullback

private theorem ordinary_scalar_arrow (l : ℕ) [Fact l.Prime] (W : Scheme.{u})
    (R : LocallyFiniteAdicRealization.Realization l W)
    (E L : Index l (PadicAlgCl l)) (h : E ≤ L)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) W) :
    (ordinary l W R).map (realizationScalarArrow l W E L h K) =
      (R.integral E).hom.app K ≫ nativeScalarTransition l W R E L h K.obj ≫
        (R.integral L).inv.app
          ((integralTransition l (PadicAlgCl l) W E L h).obj K) := by
  exact map_transport_middle (ordinary l W R)
    (inclusion (l := l) (Ω := PadicAlgCl l) (Y := W) L)
    (realizationStageObject_eq l W E L h K)
    (((stageSystem l (PadicAlgCl l) W).isoToStage
      ((inclusion (l := l) (Ω := PadicAlgCl l) (Y := W) E).obj
        ((sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) W).obj K))
      h).hom) _ _ _ _ (R.common_field E L h K)

private theorem realizationReindex_factor (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (R : LocallyFiniteAdicRealization.Realization l X)
    (S : LocallyFiniteAdicRealization.Realization l Y)
    (B : RingReindex l X g R S) (E : Index l (PadicAlgCl l))
    (I : IntegralReindex l X g B E)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) Y) :
    (realizationIntegralReindex l g R S B E I).hom.app K =
      (realizationReindexSource l g R E).hom.app K ≫ I.derived.inv.app K.obj ≫
        (derivedPull l X g B).map ((S.integral E).inv.app K) := by
  unfold realizationIntegralReindex realizationIntegralReindexData
  delta realizationReindexSource
  exact realizationReindexComposite_source _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ K

/-- The explicit integral reindexing composite commutes with coefficient enlargement.
Only the scalar square is asserted: both finite-stage natural isomorphisms have already
been constructed, and no common-stage natural transformation is assumed or produced.

Source: BS Remark 6.8.15, via Proposition 6.8.14; HRS Lemma 7.9; the mixed scalar
square in Step 4 of lem-sf-adic-realization-isomorphism-normalization.
(blueprint: lem-sf-adic-realization-reindex-scalar).

Proof in words: expand realizationReindexComposite_hom inside realizationIntegralReindex
at E and at L. The common_field
fields of R and S express their images of isoToStage by the specified finite-free
completion maps and balanced derived scalar associators. The prescribed common-stage
pullback acts on this transition by rationalPullbackScalarComparison, with the recorded
stage-transition identifications. Substitute these three formulas. On constructible
integral inputs the actual completion-unit comparison podCompletedToTower is invertible.
Its scalar square is the whole-cone scalar-extension square: the quotient coaugmentation
has zero shifted coordinate, so reindexing takes it to that same coaugmentation after
coefficient extension. Equivalently, use isomorphismComparison_scalarExtension after
identifying the specified comparison by its completion-unit normalization, then invert
its two complete-input components. The balance and representative equations of I(E)
and I(L) identify the remaining derived scalar maps with their cochain maps. On pure
sections these maps associate coefficient tensors and multiply their scalars, by the
sections fields and R.coefficient_scalar and S.coefficient_scalar. Balanced tensor
associativity therefore identifies the remaining square. The cochain counit equations
descend this equality through the good-complex localizations. Finally localization
preserves the equality; the component equation of realizationRationalReindex_existsUnique
identifies the L component with that just computed on its integral representative.
Identity extensions, zero objects, empty schemes, and ramified finite extensions use
these same normalized completion maps; no cancellation of a noninvertible ambient
completion unit is used. -/
theorem realizationIntegralReindex_scalar (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (R : LocallyFiniteAdicRealization.Realization l X)
    (S : LocallyFiniteAdicRealization.Realization l Y)
    (B : RingReindex l X g R S) (I : ∀ E, IntegralReindex l X g B E)
    (E L : Index l (PadicAlgCl l)) (h : E ≤ L)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) Y) :
    let P := (GeneralAlgebraicallyClosedCoefficients.inclusion
      (l := l) (Ω := PadicAlgCl l) (Y := Y) E).obj
        ((sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) Y).obj K)
    let t := (stageSystem l (PadicAlgCl l) Y).isoToStage P h
    (commonStageDerivedPullback l (PadicAlgCl l) g ⋙ ordinary l X R).map t.hom ≫
        (realizationRationalReindex l g R S B L (I L)).hom.app (P.toStage h) =
      (realizationIntegralReindex l g R S B E (I E)).hom.app K ≫
        (ordinary l Y S ⋙ derivedPull l X g B).map t.hom := by
  let KL := (integralTransition l (PadicAlgCl l) Y E L h).obj K
  let F := derivedPull l X g B
  let A := commonStageDerivedPullback l (PadicAlgCl l) g ⋙ ordinary l X R
  let H := ordinary l Y S ⋙ F
  let a := realizationScalarArrow l Y E L h K
  have hc : A.map a ≫
      (realizationIntegralReindex l g R S B L (I L)).hom.app KL =
    (realizationIntegralReindex l g R S B E (I E)).hom.app K ≫ H.map a := by
    exact scalar_cube F ((S.integral E).app K) ((S.integral L).app KL)
      (A.map a) _ _ _ _ _ _ _ _ _ _ _ _ _
      (realizationReindex_factor l g R S B E (I E) K)
      (realizationReindex_factor l g R S B L (I L) KL)
      (realizationReindexSource_scalar l g R E L h K)
      ((I L).derived.inv.naturality
        ((completedScalarComparison l (Coefficient.{u} l (PadicAlgCl l) E)
          (Coefficient.{u} l (PadicAlgCl l) L)
          (coefficientInclusion l (PadicAlgCl l) E L h) Y).app K.obj))
      (integralReindex_balanced_scalar l g R S B E L h (I E) (I L) K.obj)
      (ordinary_scalar_arrow l Y S E L h K)
  let T := inclusion (l := l) (Ω := PadicAlgCl l) (Y := Y) L
  let e := realizationStageObject_eq l Y E L h K
  let P := (inclusion (l := l) (Ω := PadicAlgCl l) (Y := Y) E).obj
    ((sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) Y).obj K)
  let t := (stageSystem l (PadicAlgCl l) Y).isoToStage P h
  let c := realizationRationalReindex l g R S B L (I L)
  have hcmp := (realizationRationalReindex_existsUnique l g R S B L (I L)).exists.choose_spec KL
  have hc' : A.map a ≫ c.hom.app
        ((sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) L) Y).obj KL) =
      (realizationIntegralReindex l g R S B E (I E)).hom.app K ≫ H.map a :=
    (congrArg (fun q ↦ A.map a ≫ q) hcmp).trans hc
  exact comparison_of_stage_transport T A H c e t.hom
    ((realizationIntegralReindex l g R S B E (I E)).hom.app K) hc'

end WeilConjectures.AdicQbarRealization
