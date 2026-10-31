/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.AdicRealizationFamilyData
public import WeilConjectures.SixFunctors.AdicQbarRealization.AdicRealizationPullbackInclusions

/-! # The constructed integral realization reindexing comparison

Source: Bhatt--Scholze, Remark 6.8.15; Hemo--Richarz--Scholbach, Lemma 7.9.
(blueprint: lem-sf-adic-realization-integral-reindex)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option cleanup.letToHave false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false

universe u
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization
open AlgebraicallyClosedCoefficients (Index Coefficient)
open GeneralAlgebraicallyClosedCoefficients (inclusion stageSystem)

attribute [local irreducible] HasDerivedCategory.standard
  derivedPull LocallyFiniteAdicRealization.sections
  LocallyFiniteAdicRealization.CoefficientPresentation.integralMap
  podCompletedDerivedInverseImage integralDerivedPullback
  StageSystem.ι commonStageDerivedPullback rationalDerivedPullback

section Composite

variable {A B C D E F G : Type*}
  [Category A] [Category B] [Category C] [Category D]
  [Category E] [Category F] [Category G]
  (P : A ⥤ B) (W : B ⥤ D) (V : A ⥤ E) (J : B ⥤ C) (U : A ⥤ C)
  (R : C ⥤ F) (TX : D ⥤ F) (TY : E ⥤ G) (H : E ⥤ D) (N : G ⥤ F) (Z : A ⥤ G)
  (e : U = P ⋙ J) (r : J ⋙ R ≅ W ⋙ TX) (p : V ⋙ H ≅ P ⋙ W)
  (i : TY ⋙ N ≅ H ⋙ TX) (s : Z ≅ V ⋙ TY)

/-- Abstract composite of the five prescribed integral reindexing comparisons.
Source: the integral descent composite
(blueprint: lem-sf-adic-realization-integral-reindex). -/
@[irreducible] def realizationReindexComposite : U ⋙ R ≅ Z ⋙ N :=
  Functor.isoWhiskerRight (eqToIso e) R ≪≫
    Functor.associator P J R ≪≫
    Functor.isoWhiskerLeft P r ≪≫
    (Functor.associator P W TX).symm ≪≫
    Functor.isoWhiskerRight p.symm TX ≪≫
    Functor.associator V H TX ≪≫
    Functor.isoWhiskerLeft V i.symm ≪≫
    (Functor.associator V TY N).symm ≪≫
    Functor.isoWhiskerRight s.symm N

/-- Component calculation before specializing the derived categories and coefficient maps.
Source: natural-isomorphism composition
(blueprint: lem-sf-adic-realization-integral-reindex). -/
theorem realizationReindexComposite_hom (K : A) :
    (realizationReindexComposite P W V J U R TX TY H N Z e r p i s).hom.app K =
      R.map (eqToHom (Functor.congr_obj e K)) ≫ r.hom.app (P.obj K) ≫
        TX.map (p.inv.app K) ≫ i.inv.app (V.obj K) ≫ N.map (s.inv.app K) := by
  delta realizationReindexComposite
  simp only [Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Iso.symm_hom,
    eqToIso.hom, eqToHom_app, Category.id_comp]

/-- Removing a canonical source transport leaves the same heterogeneous component.
Source: equality transport (blueprint: lem-sf-adic-realization-integral-reindex). -/
theorem realizationReindexComposite_core (K : A) :
    HEq ((realizationReindexComposite P W V J U R TX TY H N Z e r p i s).hom.app K)
      (r.hom.app (P.obj K) ≫ TX.map (p.inv.app K) ≫
        i.inv.app (V.obj K) ≫ N.map (s.inv.app K)) := by
  rw [realizationReindexComposite_hom, eqToHom_map]
  exact eqToHom_comp_heq _ _

/-- The component formula retains any prescribed pair of source equality transports.
Source: equality transport and composition of the specified isomorphisms
(blueprint: lem-sf-adic-realization-integral-reindex). -/
theorem realizationReindexComposite_normalized
    {B' : Type*} [Category B'] (Q : B ⥤ B') (L : B' ⥤ C)
    (e' : U = P ⋙ Q ⋙ L) (r' : (Q ⋙ L) ⋙ R ≅ W ⋙ TX)
    (K : A) (Z' : B') (ho : U.obj K = L.obj Z') (hr : Z' = Q.obj (P.obj K))
    (a : W.obj (P.obj K) ⟶ H.obj (V.obj K)) (ha : p.inv.app K = a) :
    HEq ((realizationReindexComposite P W V (Q ⋙ L) U R TX TY H N Z
      e' r' p i s).hom.app K)
      (R.map (eqToIso ho).hom ≫ R.map (L.map (eqToIso hr).hom) ≫
        r'.hom.app (P.obj K) ≫ TX.map a ≫
          i.inv.app (V.obj K) ≫ N.map (s.inv.app K)) := by
  subst a
  refine (realizationReindexComposite_core P W V (Q ⋙ L) U R TX TY H N Z
    e' r' p i s K).trans ?_
  symm
  simp only [eqToIso.hom, eqToHom_map, eqToHom_comp_heq_iff]
  rfl

end Composite

variable (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]
  (R : LocallyFiniteAdicRealization.Realization l X)
  (S : LocallyFiniteAdicRealization.Realization l Y)
  (B : RingReindex l X g R S) (E : Index l (PadicAlgCl l))
  (I : IntegralReindex l X g B E)

/-- An integral comparison together with its literal representative normalization.
Source: BS Remark 6.8.15; HRS Lemma 7.9.
(blueprint: lem-sf-adic-realization-integral-reindex). -/
structure IntegralRealizationReindexData where
  comparison :
    sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) Y ⋙
        inclusion (l := l) (Ω := PadicAlgCl l) (Y := Y) E ⋙
          commonStageDerivedPullback l (PadicAlgCl l) g ⋙ ordinary l X R ≅
      sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) Y ⋙
        inclusion (l := l) (Ω := PadicAlgCl l) (Y := Y) E ⋙
          ordinary l Y S ⋙ derivedPull l X g B
  agreement : ∀ c : commonStageDerivedPullback l (PadicAlgCl l) g ⋙ ordinary l X R ≅
      ordinary l Y S ⋙ derivedPull l X g B,
    (∀ K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) Y,
      HEq (c.hom.app ((inclusion (l := l) (Ω := PadicAlgCl l) (Y := Y) E).obj
        ((sfRationalConstructibleLocalization l
          (Coefficient.{u} l (PadicAlgCl l) E) Y).obj K))) (comparison.hom.app K)) →
    integralRealizationAgreement l g R S B E I c

/-- Construct both the integral isomorphism and its normalization before abstracting it.
Source: BS Remark 6.8.15; HRS Lemma 7.9.
(blueprint: lem-sf-adic-realization-integral-reindex). -/
@[irreducible] def realizationIntegralReindexData :
    IntegralRealizationReindexData l g R S B E I := by
  let QX := sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) X
  let QY := sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) Y
  let IX := inclusion (l := l) (Ω := PadicAlgCl l) (Y := X) E
  let IY := inclusion (l := l) (Ω := PadicAlgCl l) (Y := Y) E
  let P := constructibleIntegralPullback l (Coefficient.{u} l (PadicAlgCl l) E) g
  let V := (sfIntegralConstructible l (Coefficient.{u} l (PadicAlgCl l) E) Y).ι
  let W := (sfIntegralConstructible l (Coefficient.{u} l (PadicAlgCl l) E) X).ι
  let TX := pbcDerivedExtend (coefficientMap l X R E)
  let TY : DerivedCategory (integralTowerModules l
      (Coefficient.{u} l (PadicAlgCl l) E) Y) ⥤ DerivedCategory (modules l Y S) :=
    pbcDerivedExtend (coefficientMap l Y S E)
  let G := podCompletedDerivedInverseImage l (Coefficient.{u} l (PadicAlgCl l) E) g
  let F := derivedPull l X g B
  let p : V ⋙ G ≅ P ⋙ W := realizationCompletionPullbackIso l g E
  let e : QY ⋙ IY ⋙ commonStageDerivedPullback l (PadicAlgCl l) g = P ⋙ QX ⋙ IX :=
    (congrArg (fun Z ↦ QY ⋙ Z) (realizationPullback_inclusion_eq l g E)).trans
      (congrArg (fun Z ↦ Z ⋙ IX) (realizationPullback_localization_eq l g E))
  let r : (QX ⋙ IX) ⋙ ordinary l X R ≅ W ⋙ TX := by
    unfold ordinary
    exact R.integral E
  let s : (QY ⋙ IY) ⋙ ordinary l Y S ≅ V ⋙ TY := by
    unfold ordinary
    exact S.integral E
  refine ⟨realizationReindexComposite P W V (QX ⋙ IX)
    (QY ⋙ IY ⋙ commonStageDerivedPullback l (PadicAlgCl l) g) (ordinary l X R)
    TX TY G F (QY ⋙ IY ⋙ ordinary l Y S) e r p I.derived s, ?_⟩
  intro c h K
  refine (h K).trans ?_
  -- Object equations from functor equalities avoid unfolding the coefficient categories.
  have ho := Functor.congr_obj (realizationPullback_inclusion_eq l g E) (QY.obj K)
  have hr := Functor.congr_obj (realizationPullback_localization_eq l g E) K
  have hc := realizationReindexComposite_normalized
    (P := P) (W := W) (V := V)
    (U := QY ⋙ IY ⋙ commonStageDerivedPullback l (PadicAlgCl l) g)
    (R := ordinary l X R) (TX := TX) (TY := TY) (H := G) (N := F)
    (Z := QY ⋙ IY ⋙ ordinary l Y S) (p := p) (i := I.derived) (s := s)
    QX IX e r K
    ((rationalDerivedPullback l (Coefficient.{u} l (PadicAlgCl l) E) g).obj (QY.obj K))
    ho hr (podCompletedToTowerIso l (Coefficient.{u} l (PadicAlgCl l) E) g K).inv
    (realizationCompletionPullbackIso_inv_app l g E K)
  exact hc

/-- The normalized integral comparison, kept abstract with a separate component API.
Source: BS Remark 6.8.15; HRS Lemma 7.9.
(blueprint: lem-sf-adic-realization-integral-reindex). -/
@[implicit_reducible] def realizationIntegralReindex :
    sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) Y ⋙
        inclusion (l := l) (Ω := PadicAlgCl l) (Y := Y) E ⋙
          commonStageDerivedPullback l (PadicAlgCl l) g ⋙ ordinary l X R ≅
      sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) Y ⋙
        inclusion (l := l) (Ω := PadicAlgCl l) (Y := Y) E ⋙
          ordinary l Y S ⋙ derivedPull l X g B :=
  (realizationIntegralReindexData l g R S B E I).comparison

end WeilConjectures.AdicQbarRealization
