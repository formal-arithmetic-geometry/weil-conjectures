/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E3
-/
module

public import Sheaf.Paper.StrictCoefficientExchangeArrows
import all Sheaf.CategoryTheory.TowerDerivedEvaluationNormalization
import all Sheaf.CategoryTheory.ExchangeMateCube
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Sheaf.CategoryTheory.DerivedExactCube
import all Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients

/-! # Normalization of strict coefficient reduction

Source: Stacks Project, sites-cohomology.tex, Tags 0944, 0E48 and 0A07.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules.StrictQuotientExchange

private theorem adjunction_unit_ext
    {A B C : Type*} [Category A] [Category B] [Category C]
    (Q : A ⥤ B) (W : MorphismProperty A) [Q.IsLocalization W]
    {F : B ⥤ C} {R : C ⥤ B} (d d' : F ⊣ R)
    (J : A ⥤ C) (a : Q ⋙ F ≅ J)
    (h : ∀ P, d.homEquiv _ _ (a.hom.app P) =
      d'.homEquiv _ _ (a.hom.app P)) : d = d' := by
  apply Adjunction.ext
  apply Localization.natTrans_ext Q W
  intro P
  apply (cancel_mono (R.map (a.hom.app P))).mp
  simpa only [Adjunction.homEquiv_unit] using h P

private theorem adjunction_counit_ext_injective
    {A B : Type*} [Category A] [Category B]
    [Abelian A] [HasDerivedCategory.{w} A] [Abelian.HasKInjectiveResolutions A]
    {F : B ⥤ DerivedCategory.{w} A} {R : DerivedCategory.{w} A ⥤ B}
    (d d' : F ⊣ R)
    (h : ∀ I : CochainComplex A ℤ, I.IsKInjective →
      d.counit.app (DerivedCategory.Q.obj I) =
        d'.counit.app (DerivedCategory.Q.obj I)) : d = d' := by
  apply Adjunction.ext_counit
  apply Localization.natTrans_ext
    (CochainComplex.KInjectives.ι ⋙ DerivedCategory.Q)
    (CochainComplex.KInjectives.quasiIso A)
  intro I
  exact h I.obj I.property

private theorem exact_left_fac {A B : RingedTensorCorner.{u, w}}
    (e : RingedTensorEdge A B)
    [PreservesFiniteLimits e.pullback] [PreservesFiniteColimits e.pullback]
    (P : CochainComplex A.mateModules ℤ) :
    (exactLeft e).hom.app (DerivedCategory.Q.obj P) ≫
        derivedPullbackComplexComparison e.pullback e.left e.epsilon P =
      e.pullback.mapDerivedCategoryFactors.hom.app P := by
  let _ := e.isLeftDerived
  have h := Functor.leftDerivedNatTrans_app e.pullback.mapDerivedCategory e.left
    e.pullback.mapDerivedCategoryFactorsh.hom e.epsilon
    (HomotopyCategory.quasiIso A.mateModules (.up ℤ)) (𝟙 _)
    ((HomotopyCategory.quotient A.mateModules (.up ℤ)).obj P)
  have hx : (exactLeft e).hom.app (DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient A.mateModules (.up ℤ)).obj P)) ≫
        e.epsilon.app ((HomotopyCategory.quotient A.mateModules (.up ℤ)).obj P) =
      e.pullback.mapDerivedCategoryFactorsh.hom.app
        ((HomotopyCategory.quotient A.mateModules (.up ℤ)).obj P) := by
    simpa only [exactLeft, Iso.symm_hom, Functor.leftDerivedUnique,
      Functor.leftDerivedNatIso_inv, Iso.refl_inv, NatTrans.id_app, Category.comp_id] using h
  simp only [derivedPullbackComplexComparison]
  erw [← (exactLeft e).hom.naturality_assoc, reassoc_of% hx]
  change derivedPullbackComplexComparison e.pullback e.pullback.mapDerivedCategory
    e.pullback.mapDerivedCategoryFactorsh.hom P = _
  simp only [derivedPullbackComplexComparison,
    Functor.mapDerivedCategoryFactorsh_hom_app, Category.assoc,
    ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  simp only [Category.id_comp, Iso.inv_hom_id_app]
  exact Category.comp_id _


private theorem ev_comparison_fac (A : RingedTensorCorner.{u, w})
    [HasDerivedCategory.{w} A.projectionTowers] [HasCountableProducts A.mateDerived]
    (l : StrictProjectionLimit A) (n : ℕᵒᵖ)
    (P : CochainComplex A.projectionTowers ℤ) :
    (evComparison A l n).hom.app (DerivedCategory.Q.obj P) ≫
        ((CategoryTheory.evaluation ℕᵒᵖ A.mateModules).obj n).mapDerivedCategoryFactors.hom.app P =
      (l.evaluation.hom.app P).app n := by
  let b := Functor.isoWhiskerRight l.evaluation
    (CategoryTheory.evaluation ℕᵒᵖ A.mateDerived |>.obj n) ≪≫
      ((CategoryTheory.evaluation ℕᵒᵖ A.mateModules).obj n).mapDerivedCategoryFactors.symm
  let ff := Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso A.projectionTowers (.up ℤ)) A.mateDerived
  have h := congr_app (ff.map_preimage
    (X := ev A l n)
    (Y := ((CategoryTheory.evaluation ℕᵒᵖ A.mateModules).obj n).mapDerivedCategory)
    b.hom) P
  change (evComparison A l n).hom.app (DerivedCategory.Q.obj P) =
    (l.evaluation.hom.app P).app n ≫
      ((CategoryTheory.evaluation ℕᵒᵖ A.mateModules).obj n).mapDerivedCategoryFactors.inv.app P at h
  rw [h, Category.assoc, Iso.inv_hom_id_app]
  exact Category.comp_id _

section Edge

variable {A B : RingedTensorCorner.{u, w}} (e : RingedTensorEdge A B)
  [e.pushforward.Additive]
  [PreservesFiniteLimits e.pullback] [PreservesFiniteColimits e.pullback]
  [HasDerivedCategory.{w} A.projectionTowers]
  [HasDerivedCategory.{w} B.projectionTowers]
  [HasCountableProducts A.mateDerived] [HasCountableProducts B.mateDerived]
  {lA : StrictProjectionLimit A} {lB : StrictProjectionLimit B}
  {d : StrictProjectionDirectImage e lB lA}

private def right_evaluation (d : StrictProjectionDirectImage e lB lA) (n : ℕᵒᵖ) :
    d.Rt ⋙ ((CategoryTheory.evaluation ℕᵒᵖ A.mateModules).obj n).mapDerivedCategory ≅
      ((CategoryTheory.evaluation ℕᵒᵖ B.mateModules).obj n).mapDerivedCategory ⋙ e.right :=
  Functor.isoWhiskerLeft d.Rt (evComparison A lA n).symm ≪≫
    Functor.isoWhiskerRight d.evaluation (CategoryTheory.evaluation ℕᵒᵖ A.mateDerived |>.obj n) ≪≫
    Functor.isoWhiskerRight (evComparison B lB n) e.right

omit [PreservesFiniteLimits e.pullback] [PreservesFiniteColimits e.pullback] in
private theorem right_evaluation_normalized
    (d : StrictProjectionDirectImage e lB lA) (n : ℕᵒᵖ)
    (I : CochainComplex B.projectionTowers ℤ) (hI : I.IsKInjective) :
    ((CategoryTheory.evaluation ℕᵒᵖ A.mateModules).obj n).mapDerivedCategoryFactors.inv.app
      (((projectionPost e.pushforward).mapHomologicalComplex (.up ℤ)).obj I) ≫
        ((CategoryTheory.evaluation ℕᵒᵖ A.mateModules).obj n).mapDerivedCategory.map
          (d.towerEta.app I) ≫
        (right_evaluation e d n).hom.app (DerivedCategory.Q.obj I) ≫
        e.right.map
          (((CategoryTheory.evaluation ℕᵒᵖ B.mateModules).obj n).mapDerivedCategoryFactors.hom.app
            I) =
      d.eta.app (I.asFunctor.obj n) := by
  let J := ((projectionPost e.pushforward).mapHomologicalComplex (.up ℤ)).obj I
  have ha := ev_comparison_fac A lA n J
  have hai : (evComparison A lA n).inv.app (DerivedCategory.Q.obj J) ≫
      (lA.evaluation.hom.app J).app n =
      ((CategoryTheory.evaluation ℕᵒᵖ A.mateModules).obj n).mapDerivedCategoryFactors.hom.app
        J := by
    apply (cancel_epi ((evComparison A lA n).hom.app (DerivedCategory.Q.obj J))).mp
    simpa only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp] using ha.symm
  have hn := (evComparison A lA n).inv.naturality (d.towerEta.app I)
  have hd := d.evaluation_normalized I hI n
  simp only [right_evaluation, Iso.trans_hom, NatTrans.comp_app, Category.assoc]
  erw [reassoc_of% hn, ← e.right.map_comp, ev_comparison_fac]
  change _ ≫ _ ≫ (lA.ev.map (d.towerEta.app I)).app n ≫
    (d.evaluation.hom.app (DerivedCategory.Q.obj I)).app n ≫
    e.right.map ((lB.evaluation.hom.app I).app n) = _
  calc
    _ = ((CategoryTheory.evaluation ℕᵒᵖ A.mateModules).obj n).mapDerivedCategoryFactors.inv.app J ≫
        (evComparison A lA n).inv.app (DerivedCategory.Q.obj J) ≫
        (lA.evaluation.hom.app J).app n ≫ d.eta.app (I.asFunctor.obj n) := by
      exact congrArg (fun t ↦
        ((CategoryTheory.evaluation ℕᵒᵖ A.mateModules).obj n).mapDerivedCategoryFactors.inv.app J ≫
          (evComparison A lA n).inv.app (DerivedCategory.Q.obj J) ≫ t) hd
    _ = _ := by
      rw [reassoc_of% hai]
      exact Iso.inv_hom_id_app_assoc _ _ _

private theorem tower_adjunction_eq (a : TowerAdjunction e d)
    (a' : towerLeft e ⊣ d.Rt)
    (h : towerAdjunctionNormalized e d a') : a.adjunction = a' := by
  apply adjunction_unit_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso A.projectionTowers (.up ℤ)) a.adjunction a'
    ((projectionPost (I := ℕᵒᵖ) e.pullback).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q)
    (projectionPost (I := ℕᵒᵖ) e.pullback).mapDerivedCategoryFactors
  intro P
  have h1 := a.normalized P
    (((projectionPost (I := ℕᵒᵖ) e.pullback).mapHomologicalComplex (.up ℤ)).obj P) (𝟙 _)
  have h2 := h P
    (((projectionPost (I := ℕᵒᵖ) e.pullback).mapHomologicalComplex (.up ℤ)).obj P) (𝟙 _)
  erw [DerivedCategory.Q.map_id, Category.comp_id] at h1 h2
  exact h1.trans h2.symm

private theorem ambient_adjunction_eq
    (a' : e.pullback.mapDerivedCategory ⊣ e.right)
    (h : ∀ (M : CochainComplex A.mateModules ℤ) (I : CochainComplex B.mateModules ℤ)
      (b : (e.pullback.mapHomologicalComplex (.up ℤ)).obj M ⟶ I),
      a'.homEquiv (DerivedCategory.Q.obj M) (DerivedCategory.Q.obj I)
          (e.pullback.mapDerivedCategoryFactors.hom.app M ≫ DerivedCategory.Q.map b) =
        DerivedCategory.Q.map
          ((e.moduleAdjunction.mapHomologicalComplex (.up ℤ)).homEquiv M I b) ≫
          d.eta.app I) :
    e.derivedAdjunction.ofNatIsoLeft (exactLeft e).symm = a' := by
  let : HasSheafify B.topology AddCommGrpCat.{u} :=
    GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian _ _
  let : B.topology.WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance
  let : IsGrothendieckAbelian.{u} B.mateModules :=
    SheafOfModules.isGrothendieckAbelian _
  apply adjunction_counit_ext_injective
  intro I hI
  have _ := d.computes I hI
  apply (cancel_epi (e.pullback.mapDerivedCategory.map (d.eta.app I))).mp
  change e.pullback.mapDerivedCategory.map (d.eta.app I) ≫
      (exactLeft e).hom.app (e.right.obj (DerivedCategory.Q.obj I)) ≫
      e.derivedAdjunction.counit.app (DerivedCategory.Q.obj I) = _
  have hn := (exactLeft e).hom.naturality (d.eta.app I)
  erw [← Category.assoc, hn, Category.assoc, d.counit_normalized I hI,
    ← Category.assoc, exact_left_fac]
  exact (counitOfHomFormula e.pullback e.pushforward e.moduleAdjunction e.right
    d.eta a' h I).symm

private theorem right_evaluation_counit
    (a : TowerAdjunction e d) (n : ℕᵒᵖ)
    (M : DerivedCategory B.projectionTowers) :
    ((CategoryTheory.evaluation ℕᵒᵖ B.mateModules).obj n).mapDerivedCategory.map
        (a.adjunction.counit.app M) =
      (leftEvaluation e n).hom.app (d.Rt.obj M) ≫
        e.left.map ((right_evaluation e d n).hom.app M) ≫
        e.derivedAdjunction.counit.app
          (((CategoryTheory.evaluation ℕᵒᵖ B.mateModules).obj n).mapDerivedCategory.obj M) := by
  let : HasSheafify A.topology AddCommGrpCat.{u} :=
    GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian _ _
  let : A.topology.WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance
  let : IsGrothendieckAbelian.{u} A.mateModules :=
    SheafOfModules.isGrothendieckAbelian _
  let : HasSheafify B.topology AddCommGrpCat.{u} :=
    GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian _ _
  let : B.topology.WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance
  let : IsGrothendieckAbelian.{u} B.mateModules :=
    SheafOfModules.isGrothendieckAbelian _
  let : IsGrothendieckAbelian.{u} A.projectionTowers := tower_grothendieck A.mateModules
  let : IsGrothendieckAbelian.{u} B.projectionTowers := tower_grothendieck B.mateModules
  let _ := d.derived
  let _ := d.towerDerived
  obtain ⟨ad, adT, had, hadT, β, _, hu, _, hc⟩ :=
    exists_unique_towerDerivedEvaluation_normalized e.pullback e.pushforward
      e.moduleAdjunction e.right d.Rt d.eta d.towerEta
  have ht := tower_adjunction_eq e a adT hadT
  have ha := ambient_adjunction_eq e (d := d) ad had
  have hb : right_evaluation e d n = β n :=
    hu n (right_evaluation e d n) (fun I hI ↦ right_evaluation_normalized e d n I hI)
  have H := hc n M
  rw [← ht, ← ha, ← hb] at H
  change _ = (towerDerivedEvaluationInterchange e.pullback n).hom.app _ ≫
    e.pullback.mapDerivedCategory.map ((right_evaluation e d n).hom.app M) ≫
    (exactLeft e).hom.app _ ≫ e.derivedAdjunction.counit.app _ at H
  erw [(exactLeft e).hom.naturality_assoc] at H
  simpa only [leftEvaluation, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Category.assoc] using H

end Edge

section Square

private theorem inverse_square
    {C : Type*} [Category C] {A0 A1 A2 B0 B1 B2 : C}
    (i : A0 ≅ A1) (j : A1 ≅ A2) (k : B0 ≅ B1) (l : B1 ≅ B2)
    (x : A0 ⟶ B0) (y : A2 ⟶ B2)
    (h : x ≫ k.hom ≫ l.hom = i.hom ≫ j.hom ≫ y) :
    j.inv ≫ i.inv ≫ x = y ≫ l.inv ≫ k.inv := by
  apply (cancel_mono (k.hom ≫ l.hom)).mp
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [h]
  simp only [Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]


attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private def ambient_composite
    {A B C : RingedTensorCorner.{u, w}}
    (f : RingedTensorEdge A B) (h : RingedTensorEdge B C)
    [PreservesFiniteLimits f.pullback] [PreservesFiniteColimits f.pullback]
    [PreservesFiniteLimits h.pullback] [PreservesFiniteColimits h.pullback] :
    f.pullback.mapDerivedCategory ⋙ h.pullback.mapDerivedCategory ≅ f.left ⋙ h.left :=
  Functor.isoWhiskerLeft f.pullback.mapDerivedCategory (exactLeft h) ≪≫
    Functor.isoWhiskerRight (exactLeft f) h.left

private theorem ambient_composite_fac
    {A B C : RingedTensorCorner.{u, w}}
    (f : RingedTensorEdge A B) (h : RingedTensorEdge B C)
    [PreservesFiniteLimits f.pullback] [PreservesFiniteColimits f.pullback]
    [PreservesFiniteLimits h.pullback] [PreservesFiniteColimits h.pullback]
    (P : CochainComplex A.mateModules ℤ) :
    (ambient_composite f h).hom.app (DerivedCategory.Q.obj P) ≫
        h.left.map (derivedPullbackComplexComparison f.pullback f.left f.epsilon P) ≫
        derivedPullbackComplexComparison h.pullback h.left h.epsilon
          ((f.pullback.mapHomologicalComplex (.up ℤ)).obj P) =
      h.pullback.mapDerivedCategory.map (f.pullback.mapDerivedCategoryFactors.hom.app P) ≫
        h.pullback.mapDerivedCategoryFactors.hom.app
          ((f.pullback.mapHomologicalComplex (.up ℤ)).obj P) := by
  simp only [ambient_composite, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc]
  erw [← h.left.map_comp_assoc, exact_left_fac, ← (exactLeft h).hom.naturality_assoc,
    exact_left_fac]

private theorem ambient_square
    {S T X Y : RingedTensorCorner.{u, w}}
    {f : RingedTensorEdge S X} {g : RingedTensorEdge S T}
    {h : RingedTensorEdge X Y} {e : RingedTensorEdge T Y}
    [PreservesFiniteLimits f.pullback] [PreservesFiniteColimits f.pullback]
    [PreservesFiniteLimits g.pullback] [PreservesFiniteColimits g.pullback]
    [PreservesFiniteLimits h.pullback] [PreservesFiniteColimits h.pullback]
    [PreservesFiniteLimits e.pullback] [PreservesFiniteColimits e.pullback]
    (s : RingedTensorSquare S T X Y g f e h) :
    s.derivedComparison = (ambient_composite f h).symm ≪≫
      Functor.face f.pullback h.pullback g.pullback e.pullback s.modules ≪≫
        ambient_composite g e := by
  apply s.derivedComparison_existsUnique.unique
    (Classical.choose_spec s.derivedComparison_existsUnique.exists)
  intro P _ _
  apply (cancel_epi ((ambient_composite f h).hom.app (DerivedCategory.Q.obj P))).mp
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc,
    Iso.hom_inv_id_app_assoc]
  erw [ambient_composite_fac g e P]
  erw [reassoc_of% (ambient_composite_fac f h P)]
  exact Functor.face_fac f.pullback h.pullback g.pullback e.pullback s.modules P

private theorem exact_refl
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    Functor.mapDerivedCategoryNatIso (Iso.refl F) = Iso.refl F.mapDerivedCategory := by
  apply Iso.ext
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso A (.up ℤ))
  intro P
  apply (cancel_mono (F.mapDerivedCategoryFactors.hom.app P)).mp
  have H := Functor.mapDerivedCategoryNatIso_fac (Iso.refl F) P
  change _ = _ ≫ DerivedCategory.Q.map (𝟙 _) at H
  erw [DerivedCategory.Q.map_id, Category.comp_id] at H
  simpa only [Iso.refl_hom, NatTrans.id_app, Category.id_comp] using H

private theorem evaluation_pair
    {A B C : RingedTensorCorner.{u, w}}
    (f : RingedTensorEdge A B) (h : RingedTensorEdge B C)
    [PreservesFiniteLimits f.pullback] [PreservesFiniteColimits f.pullback]
    [PreservesFiniteLimits h.pullback] [PreservesFiniteColimits h.pullback]
    [HasDerivedCategory.{w} A.projectionTowers]
    [HasDerivedCategory.{w} B.projectionTowers]
    [HasDerivedCategory.{w} C.projectionTowers]
    (n : ℕᵒᵖ) (M : DerivedCategory A.projectionTowers) :
    (leftEvaluation h n).hom.app ((towerLeft f).obj M) ≫
        h.left.map ((leftEvaluation f n).hom.app M) =
      (towerDerivedEvaluationInterchange h.pullback n).hom.app ((towerLeft f).obj M) ≫
        h.pullback.mapDerivedCategory.map
          ((towerDerivedEvaluationInterchange f.pullback n).hom.app M) ≫
        (ambient_composite f h).hom.app
          (((CategoryTheory.evaluation ℕᵒᵖ A.mateModules).obj n).mapDerivedCategory.obj M) := by
  simp only [leftEvaluation, ambient_composite, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.map_comp, Category.assoc]
  erw [← (exactLeft h).hom.naturality_assoc]
  rfl

private theorem pullback_evaluation_square
    {S T X Y : RingedTensorCorner.{u, w}}
    {f : RingedTensorEdge S X} {g : RingedTensorEdge S T}
    {h : RingedTensorEdge X Y} {e : RingedTensorEdge T Y}
    [PreservesFiniteLimits f.pullback] [PreservesFiniteColimits f.pullback]
    [PreservesFiniteLimits g.pullback] [PreservesFiniteColimits g.pullback]
    [PreservesFiniteLimits h.pullback] [PreservesFiniteColimits h.pullback]
    [PreservesFiniteLimits e.pullback] [PreservesFiniteColimits e.pullback]
    [HasDerivedCategory.{w} S.projectionTowers]
    [HasDerivedCategory.{w} T.projectionTowers]
    [HasDerivedCategory.{w} X.projectionTowers]
    [HasDerivedCategory.{w} Y.projectionTowers]
    (s : RingedTensorSquare S T X Y g f e h) (n : ℕᵒᵖ)
    (M : DerivedCategory S.projectionTowers) :
    h.left.map ((leftEvaluation f n).inv.app M) ≫
        (leftEvaluation h n).inv.app ((towerLeft f).obj M) ≫
        ((CategoryTheory.evaluation ℕᵒᵖ Y.mateModules).obj n).mapDerivedCategory.map
          ((towerSquare f g h e s).hom.app M) =
      s.derivedComparison.hom.app
          (((CategoryTheory.evaluation ℕᵒᵖ S.mateModules).obj n).mapDerivedCategory.obj M) ≫
        e.left.map ((leftEvaluation g n).inv.app M) ≫
        (leftEvaluation e n).inv.app ((towerLeft g).obj M) := by
  let ES := (CategoryTheory.evaluation ℕᵒᵖ S.mateModules).obj n
  let ET := (CategoryTheory.evaluation ℕᵒᵖ T.mateModules).obj n
  let EX := (CategoryTheory.evaluation ℕᵒᵖ X.mateModules).obj n
  let EY := (CategoryTheory.evaluation ℕᵒᵖ Y.mateModules).obj n
  have C := Functor.mapDerivedCategory_exactCube
    (projectionPost (I := ℕᵒᵖ) f.pullback) (projectionPost h.pullback) EY
    (projectionPost g.pullback) (projectionPost e.pullback) ET e.pullback
    ES g.pullback EX h.pullback f.pullback
    ((Functor.whiskeringRight ℕᵒᵖ S.mateModules Y.mateModules).mapIso s.modules)
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) s.modules
    (by
      intro P
      change s.modules.hom.app (P.obj n) ≫ 𝟙 _ ≫ e.pullback.map (𝟙 _) =
        h.pullback.map (𝟙 _) ≫ s.modules.hom.app (P.obj n)
      erw [e.pullback.map_id, h.pullback.map_id]
      rw [Category.id_comp]
      exact Category.comp_id _)
  simp only [exact_refl] at C
  have D : EY.mapDerivedCategory.map ((towerSquare f g h e s).hom.app M) ≫
      (towerDerivedEvaluationInterchange e.pullback n).hom.app ((towerLeft g).obj M) ≫
      e.pullback.mapDerivedCategory.map
        ((towerDerivedEvaluationInterchange g.pullback n).hom.app M) =
      (towerDerivedEvaluationInterchange h.pullback n).hom.app ((towerLeft f).obj M) ≫
      h.pullback.mapDerivedCategory.map
        ((towerDerivedEvaluationInterchange f.pullback n).hom.app M) ≫
      (Functor.face f.pullback h.pullback g.pullback e.pullback s.modules).hom.app
        (ES.mapDerivedCategory.obj M) := by
    simpa only [towerSquare, towerDerivedEvaluationInterchange, Functor.face, exact_refl,
      Iso.trans_hom, Iso.symm_hom, Iso.refl_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      NatTrans.id_app, Functor.map_id, Category.id_comp, Category.comp_id, Category.assoc]
      using congr_app C M
  apply inverse_square
    ((leftEvaluation h n).app ((towerLeft f).obj M))
    (h.left.mapIso ((leftEvaluation f n).app M))
    ((leftEvaluation e n).app ((towerLeft g).obj M))
    (e.left.mapIso ((leftEvaluation g n).app M))
  change _ ≫ (leftEvaluation e n).hom.app _ ≫
      e.left.map ((leftEvaluation g n).hom.app M) =
    (leftEvaluation h n).hom.app _ ≫
      h.left.map ((leftEvaluation f n).hom.app M) ≫ _
  rw [evaluation_pair g e n M]
  erw [reassoc_of% (evaluation_pair f h n M)]
  rw [ambient_square s]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Iso.hom_inv_id_app_assoc]
  simpa only [Category.assoc] using congrArg
    (fun t ↦ t ≫ (ambient_composite g e).hom.app (ES.mapDerivedCategory.obj M)) D

end Square

private theorem mate_of_counit
    {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
    {F : A ⥤ B} {R : B ⥤ A} {F' : A' ⥤ B'} {R' : B' ⥤ A'}
    (adj : F ⊣ R) (adj' : F' ⊣ R')
    (a : A ⥤ A') (b : B ⥤ B') (p : F ⋙ b ≅ a ⋙ F')
    (r : R ⋙ a ⟶ b ⋙ R')
    (hr : ∀ E : B, b.map (adj.counit.app E) =
      p.hom.app (R.obj E) ≫ F'.map (r.app E) ≫ adj'.counit.app (b.obj E))
    (E : B) :
    (mateEquiv adj adj' (TwoSquare.mk a F F' b p.inv)).app E = r.app E := by
  apply (adj'.homEquiv _ _).symm.injective
  change F'.map (_) ≫ adj'.counit.app _ = _
  rw [mateEquiv_counit, hr]
  simp only [Iso.inv_hom_id_app_assoc]
  rfl

private theorem mate_transport
    {S T X Y : Type*} [Category S] [Category T] [Category X] [Category Y]
    (F : S ⥤ X) (G : T ⥤ S) (E : T ⥤ Y) (H : Y ⥤ X)
    (β : G ⋙ F ⟶ E ⋙ H)
    {A0 A1 B0 B1 : X} {C0 C1 : S} {D0 D1 : T} {Z0 Z1 : Y}
    (a : A0 ≅ A1) (b : B0 ≅ B1) (c : C0 ≅ C1) (d : D0 ≅ D1)
    (p : A1 ≅ F.obj C1) (r : C0 ≅ G.obj D0)
    (s : B0 ≅ H.obj Z0) (z : Z0 ≅ Z1) (q : Z1 ≅ E.obj D1)
    (u : A0 ⟶ B0) (v : A1 ⟶ B1)
    (hn : u ≫ b.hom = a.hom ≫ v)
    (hv : v ≫ b.inv ≫ s.hom ≫ H.map z.hom ≫ H.map q.hom =
      p.hom ≫ F.map (c.inv ≫ r.hom ≫ G.map d.hom) ≫ β.app D1) :
    u ≫ s.hom ≫ H.map z.hom ≫ H.map q.hom ≫ H.map (E.map d.inv) =
      a.hom ≫ p.hom ≫ F.map c.inv ≫ F.map r.hom ≫ β.app D0 := by
  have ht := congrArg (fun t ↦ a.hom ≫ t) hv
  simp only [← Category.assoc] at ht
  rw [← hn] at ht
  simp only [Category.assoc, Iso.hom_inv_id_assoc] at ht
  rw [reassoc_of% ht]
  simp only [Functor.map_comp, Category.assoc]
  have hβ := β.naturality d.inv
  dsimp only [Functor.comp_map] at hβ
  rw [← hβ]
  have hi : F.map (G.map d.hom) ≫ F.map (G.map d.inv) = 𝟙 _ := by
    rw [← F.map_comp, ← G.map_comp, Iso.hom_inv_id, G.map_id, F.map_id]
  rw [← Category.assoc (F.map (G.map d.hom)), hi, Category.id_comp]

variable {S T X Y : RingedTensorCorner.{u, w}}
  (f : RingedTensorEdge S X) (g : RingedTensorEdge S T)
  (h : RingedTensorEdge X Y) (e : RingedTensorEdge T Y)
  [PreservesFiniteLimits f.pullback] [PreservesFiniteColimits f.pullback]
  [PreservesFiniteLimits g.pullback] [PreservesFiniteColimits g.pullback]
  [PreservesFiniteLimits h.pullback] [PreservesFiniteColimits h.pullback]
  [PreservesFiniteLimits e.pullback] [PreservesFiniteColimits e.pullback]
  [HasDerivedCategory.{w} S.projectionTowers]
  [HasDerivedCategory.{w} T.projectionTowers]
  [HasDerivedCategory.{w} X.projectionTowers]
  [HasDerivedCategory.{w} Y.projectionTowers]

variable [g.pushforward.Additive] [h.pushforward.Additive]
  [HasCountableProducts S.mateDerived] [HasCountableProducts T.mateDerived]
  [HasCountableProducts X.mateDerived] [HasCountableProducts Y.mateDerived]
  {lS : StrictProjectionLimit S} {lT : StrictProjectionLimit T}
  {lX : StrictProjectionLimit X} {lY : StrictProjectionLimit Y}
  {dg : StrictProjectionDirectImage g lT lS} {dh : StrictProjectionDirectImage h lY lX}

variable {f g h e}

/-- Evaluation of the actual strict tower mate is the ambient mate.
Source: Stacks Project, Tag 0A07 and the counit transpose formula of Tag 0E48
(blueprint: lem-sbc-strict-tower-mate-evaluation).

Proof: Form the inverse-image cube between the exact derived tower square and
the ambient derived square using normalized evaluation. Its faces commute on
complexes by evaluation of termwise pullback and the given ordinary module square.
Localization preserves this equation. The tower and ambient adjunctions are the
normalized derived adjunctions: their Hom formulas determine them uniquely.
The evaluation normalization of the direct-image comparisons on K-injective towers
therefore identifies their evaluated counits, by the unique normalized evaluation
theorem. Apply the mate-cube identity to that inverse-image cube. Substitute the
counit-preserving direct-image comparisons and reassociate the four evaluation
comparisons. Their composites are exactly evaluatedSource and evaluatedTarget.
This proves the equation for every strict derived tower, hence for input q K.
No conservativity or faithfulness assertion about evaluated morphisms is needed. -/
theorem strictTowerMateEvaluation
    (s : RingedTensorSquare S T X Y g f e h) (q : Coefficients f g h e s)
    (ag : TowerAdjunction g dg) (ah : TowerAdjunction h dh)
    (K : T.mateDerived) (n : ℕᵒᵖ) :
    (ev X lX n).map ((towerMate f g h e s ag ah).app (input q K)) ≫
        (evaluatedTarget q dh K n).hom =
      (evaluatedSource q dg K n).hom ≫
        s.exchange.app ((ev T lT n).obj (input q K)) := by
  let ES := ((CategoryTheory.evaluation ℕᵒᵖ S.mateModules).obj n).mapDerivedCategory
  let ET := ((CategoryTheory.evaluation ℕᵒᵖ T.mateModules).obj n).mapDerivedCategory
  let EX := ((CategoryTheory.evaluation ℕᵒᵖ X.mateModules).obj n).mapDerivedCategory
  let EY := ((CategoryTheory.evaluation ℕᵒᵖ Y.mateModules).obj n).mapDerivedCategory
  have hg' := mate_of_counit ag.adjunction g.derivedAdjunction ES ET
    (leftEvaluation g n) (right_evaluation g dg n).hom
    (right_evaluation_counit g ag n) (input q K)
  have hh' := mate_of_counit ah.adjunction h.derivedAdjunction EX EY
    (leftEvaluation h n) (right_evaluation h dh n).hom
    (right_evaluation_counit h ah n) ((towerLeft e).obj (input q K))
  have hcub := exchangeMate_cube_all_normalized ag.adjunction ah.adjunction
    g.derivedAdjunction h.derivedAdjunction ES ET EX EY
    (leftEvaluation g n) (leftEvaluation f n) (leftEvaluation e n) (leftEvaluation h n)
    (towerSquare f g h e s).hom s.derivedComparison.hom
    (pullback_evaluation_square s n) (input q K)
    ((right_evaluation g dg n).hom.app (input q K))
    ((right_evaluation h dh n).hom.app ((towerLeft e).obj (input q K)))
    ((towerMate f g h e s ag ah).app (input q K))
    (s.exchange.app (ET.obj (input q K))) (by rfl)
    (by unfold RingedTensorSquare.exchange; rfl) hg' hh' 
  have H := mate_transport f.left g.right e.left h.right s.exchange
    ((evComparison X lX n).app (upper q dg K))
    ((evComparison X lX n).app (lower q dh K))
    ((evComparison S lS n).app (dg.Rt.obj (input q K)))
    ((evComparison T lT n).app (input q K))
    ((leftEvaluation f n).app (dg.Rt.obj (input q K)))
    ((Functor.isoWhiskerRight dg.evaluation
      ((CategoryTheory.evaluation ℕᵒᵖ S.mateDerived).obj n)).app (input q K))
    ((Functor.isoWhiskerRight dh.evaluation
      ((CategoryTheory.evaluation ℕᵒᵖ X.mateDerived).obj n)).app
        ((towerLeft e).obj (input q K)))
    ((evComparison Y lY n).app ((towerLeft e).obj (input q K)))
    ((leftEvaluation e n).app (input q K))
    ((ev X lX n).map ((towerMate f g h e s ag ah).app (input q K)))
    (EX.map ((towerMate f g h e s ag ah).app (input q K)))
    ((evComparison X lX n).hom.naturality
      ((towerMate f g h e s ag ah).app (input q K)))
    (by
      simpa only [right_evaluation, Iso.app_hom, Iso.app_inv, Iso.trans_hom, Iso.symm_hom,
        NatTrans.comp_app,
        Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
        Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.map_comp,
        RingedTensorSquare.exchange, towerMate, Category.assoc] using hcub)
  simpa only [evaluatedSource, evaluatedTarget, Iso.app_hom, Iso.app_inv, 
    Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.mapIso_hom, Functor.map_comp, Category.assoc] using H

end SheafOfModules.StrictQuotientExchange
