/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import Submission.WeilConjectures.CategoryTheory.SmoothBaseChange.TowerDerivedEvaluationNormalization
public import Mathlib.CategoryTheory.Functor.OfSequence
import Submission.WeilConjectures.Algebra.Homology.TowerEvaluationKInjective

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Unbounded right derivation commutes with tower evaluation

Source: Stacks Project, Sites Cohomology, Tag 0941, proof of
`lemma-derived-limit-is-ok`, and Derived Categories, Tags 070I, 070Y and 070K;
additive-functor generalization (blueprint: lem-coef-tower-right-derived-evaluation).

The units and resolution comparisons are those of
`Functor.rightDerivedFunctorOfQuasiIsoResolutions`. Natural number `n` denotes positive
level `n + 1`. No exactness or adjunction assumption is imposed on the additive functor.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe uA vA uB vB wA wB wTA wTB

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.TowerRightDerivedEvaluation

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- Descend a comparison invertible on K-injectives, using the Hom bijection of
Stacks Tag 070I. Naturality along a resolution gives normalization on all complexes. -/
private theorem descend_comparison
    {C : Type uA} {D : Type uB} [Category.{vA} C] [Category.{vB} D]
    [Abelian C] [HasDerivedCategory.{wA} C]
    (enough : ∀ K : CochainComplex C ℤ,
      ∃ (I : CochainComplex C ℤ) (a : K ⟶ I), I.IsKInjective ∧ QuasiIso a)
    (R S : DerivedCategory C ⥤ D) (H : CochainComplex C ℤ ⥤ D)
    (a : H ⟶ DerivedCategory.Q ⋙ R) (b : H ⟶ DerivedCategory.Q ⋙ S)
    (ha : ∀ I : CochainComplex C ℤ, I.IsKInjective → IsIso (a.app I))
    (hb : ∀ I : CochainComplex C ℤ, I.IsKInjective → IsIso (b.app I)) :
    ∃ β : R ≅ S, ∀ K : CochainComplex C ℤ,
      a.app K ≫ β.hom.app (DerivedCategory.Q.obj K) = b.app K := by
  classical
  let π := HomotopyCategory.quotient C (.up ℤ)
  let Q : CochainComplex C ℤ ⥤ DerivedCategory C := DerivedCategory.Q
  let d (I : CochainComplex C ℤ) (hI : I.IsKInjective) :
      R.obj (Q.obj I) ⟶ S.obj (Q.obj I) :=
    letI := ha I hI
    inv (a.app I) ≫ b.app I
  have dn (I J : CochainComplex C ℤ) (hI : I.IsKInjective) (hJ : J.IsKInjective)
      (f : I ⟶ J) :
      R.map (Q.map f) ≫ d J hJ = d I hI ≫ S.map (Q.map f) := by
    have := ha I hI
    have := ha J hJ
    apply (cancel_epi (a.app I)).mp
    change a.app I ≫ (R.map (Q.map f) ≫ (inv (a.app J) ≫ b.app J)) =
      a.app I ≫ ((inv (a.app I) ≫ b.app I) ≫ S.map (Q.map f))
    have an := a.naturality f
    dsimp only [Functor.comp_map] at an
    rw [← Category.assoc, ← an]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    exact b.naturality f
  have dn' (I J : CochainComplex C ℤ) (hI : I.IsKInjective) (hJ : J.IsKInjective)
      (f : Q.obj I ⟶ Q.obj J) :
      R.map f ≫ d J hJ = d I hI ≫ S.map f := by
    let q := DerivedCategory.quotientCompQhIso C
    obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective (π.obj I) J).surjective
      (q.hom.app I ≫ f ≫ q.inv.app J)
    obtain ⟨g, rfl⟩ := π.map_surjective g
    have hgf : Q.map g = f := by
      have hn := q.hom.naturality g
      change DerivedCategory.Qh.map (π.map g) ≫ q.hom.app J =
        q.hom.app I ≫ Q.map g at hn
      rw [hg] at hn
      simp only [Category.assoc] at hn
      erw [Iso.inv_hom_id_app, Category.comp_id] at hn
      exact (cancel_epi (q.hom.app I)).mp hn.symm
    rw [← hgf]
    exact dn I J hI hJ g
  choose J f hJ hf using fun K ↦ enough K
  let j (X : DerivedCategory C) := J (Q.objPreimage X)
  have hj (X : DerivedCategory C) : (j X).IsKInjective := hJ _
  have hq (K : CochainComplex C ℤ) : IsIso (Q.map (f K)) := by
    have := hf K
    infer_instance
  let e (X : DerivedCategory C) : X ≅ Q.obj (j X) :=
    (Q.objObjPreimageIso X).symm ≪≫ asIso (Q.map (f (Q.objPreimage X)))
  let c (X : DerivedCategory C) := R.map (e X).hom ≫ d (j X) (hj X) ≫ S.map (e X).inv
  have cn {X Y : DerivedCategory C} (f : X ⟶ Y) :
      R.map f ≫ c Y = c X ≫ S.map f := by
    have ht := dn' (j X) (j Y) (hj X) (hj Y) ((e X).inv ≫ f ≫ (e Y).hom)
    have ht' := congrArg (fun t ↦ R.map (e X).hom ≫ t ≫ S.map (e Y).inv) ht
    simpa only [c, Functor.map_comp, Category.assoc, Iso.hom_inv_id_map_assoc,
      Iso.inv_hom_id_map_assoc, Iso.hom_inv_id_map, Category.comp_id] using ht'
  have ci (X : DerivedCategory C) : IsIso (c X) := by
    have := ha (j X) (hj X)
    have := hb (j X) (hj X)
    dsimp only [c, d]
    infer_instance
  let β : R ≅ S := NatIso.ofComponents (fun X ↦ asIso (c X)) (fun f ↦ cn f)
  have atI (I : CochainComplex C ℤ) (hI : I.IsKInjective) :
      β.hom.app (Q.obj I) = d I hI := by
    have ht := dn' (j (Q.obj I)) I (hj _) hI (e (Q.obj I)).inv
    have ht' := congrArg (fun t ↦ R.map (e (Q.obj I)).hom ≫ t) ht
    change c (Q.obj I) = _
    simpa only [c, Category.assoc, Iso.hom_inv_id_map_assoc] using ht'.symm
  refine ⟨β, ?_⟩
  intro K
  obtain ⟨I, f, hI, hf⟩ := enough K
  have := ha I hI
  have hnorm : a.app I ≫ β.hom.app (Q.obj I) = b.app I := by
    rw [atI I hI]
    exact IsIso.hom_inv_id_assoc _ _
  apply (cancel_mono (S.map (Q.map f))).mp
  rw [Category.assoc, ← β.hom.naturality, ← Category.assoc]
  have an := a.naturality f
  dsimp only [Functor.comp_map] at an
  rw [← an]
  rw [Category.assoc, hnorm]
  exact b.naturality f

private theorem derived_ext
    {C : Type uA} {D : Type uB} [Category.{vA} C] [Category.{vB} D]
    [Abelian C] [HasDerivedCategory.{wA} C]
    (enough : ∀ K : CochainComplex C ℤ,
      ∃ (I : CochainComplex C ℤ) (a : K ⟶ I), I.IsKInjective ∧ QuasiIso a)
    {R S : DerivedCategory C ⥤ D} (α β : R ⟶ S)
    (h : ∀ I : CochainComplex C ℤ, I.IsKInjective →
      α.app (DerivedCategory.Q.obj I) = β.app (DerivedCategory.Q.obj I)) : α = β := by
  apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
  intro K
  obtain ⟨I, f, hI, hf⟩ := enough K
  apply (cancel_mono (S.map (DerivedCategory.Q.map f))).mp
  rw [← α.naturality, ← β.naturality, h I hI]

private theorem towerTransition_fac
    (A : Type uA) [Category.{vA} A] [Abelian A]
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ A)]
    {m n : ℕᵒᵖ} (t : m ⟶ n) (J : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (towerDerivedEvaluationTransition A t).app (DerivedCategory.Q.obj J) ≫
        ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategoryFactors.hom.app J =
      ((evaluation ℕᵒᵖ A).obj m).mapDerivedCategoryFactors.hom.app J ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex ((evaluation ℕᵒᵖ A).map t) (.up ℤ)).app J) := by
  have hm : Localization.Lifting.iso DerivedCategory.Q
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ))
      (((evaluation ℕᵒᵖ A).obj m).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
      ((evaluation ℕᵒᵖ A).obj m).mapDerivedCategory =
        ((evaluation ℕᵒᵖ A).obj m).mapDerivedCategoryFactors := rfl
  have hn : Localization.Lifting.iso DerivedCategory.Q
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ))
      (((evaluation ℕᵒᵖ A).obj n).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
      ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategory =
        ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategoryFactors := rfl
  simp [towerDerivedEvaluationTransition, Localization.liftNatTrans_app, hm, hn]

private theorem towerTransition_inv_fac
    (A : Type uA) [Category.{vA} A] [Abelian A]
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ A)]
    {m n : ℕᵒᵖ} (t : m ⟶ n) (J : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    ((evaluation ℕᵒᵖ A).obj m).mapDerivedCategoryFactors.inv.app J ≫
        (towerDerivedEvaluationTransition A t).app (DerivedCategory.Q.obj J) =
      DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex ((evaluation ℕᵒᵖ A).map t) (.up ℤ)).app J) ≫
        ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategoryFactors.inv.app J := by
  apply (cancel_mono
    (((evaluation ℕᵒᵖ A).obj n).mapDerivedCategoryFactors.hom.app J)).mp
  simp only [Category.assoc, towerTransition_fac, Iso.inv_hom_id_app_assoc,
    Iso.inv_hom_id_app]
  exact (Category.comp_id _).symm

end CategoryTheory.TowerRightDerivedEvaluation
