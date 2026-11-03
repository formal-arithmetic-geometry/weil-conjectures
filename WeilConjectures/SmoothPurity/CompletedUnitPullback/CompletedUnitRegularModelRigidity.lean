/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedUnitPullback.CompletedUnitRegularModelData
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-! # Rigidity of the regular normalized pullback model -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.CompletedUnitPullback

attribute [local implicit_reducible] PrimitiveCounit.pull

private theorem q_map_bijective_single_support
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (C D : CochainComplex A ℤ)
    (hC : ∀ i : ℤ, i ≠ 0 → IsZero (C.X i))
    (hD : ∀ i : ℤ, i ≠ 0 → IsZero (D.X i)) :
    Function.Bijective (DerivedCategory.Q.map : (C ⟶ D) → _) := by
  let : C.IsStrictlyGE 0 := (CochainComplex.isStrictlyGE_iff C 0).2
    (fun i hi ↦ hC i (by lia))
  let : C.IsStrictlyLE 0 := (CochainComplex.isStrictlyLE_iff C 0).2
    (fun i hi ↦ hC i (by lia))
  let : D.IsStrictlyGE 0 := (CochainComplex.isStrictlyGE_iff D 0).2
    (fun i hi ↦ hD i (by lia))
  let : D.IsStrictlyLE 0 := (CochainComplex.isStrictlyLE_iff D 0).2
    (fun i hi ↦ hD i (by lia))
  obtain ⟨M, ⟨e⟩⟩ := C.exists_iso_single 0
  obtain ⟨N, ⟨e'⟩⟩ := D.exists_iso_single 0
  change C ≅ (CochainComplex.singleFunctor A 0).obj M at e
  change D ≅ (CochainComplex.singleFunctor A 0).obj N at e'
  have hs : Function.Bijective (DerivedCategory.Q.map :
      ((CochainComplex.singleFunctor A 0).obj M ⟶
        (CochainComplex.singleFunctor A 0).obj N) → _) := by
    constructor
    · intro a b hab
      obtain ⟨a, rfl⟩ := (CochainComplex.singleFunctor A 0).map_surjective a
      obtain ⟨b, rfl⟩ := (CochainComplex.singleFunctor A 0).map_surjective b
      exact congrArg (CochainComplex.singleFunctor A 0).map
        ((DerivedCategory.singleFunctor A 0).map_injective hab)
    · intro a
      obtain ⟨b, hb⟩ := (DerivedCategory.singleFunctor A 0).map_surjective a
      exact ⟨(CochainComplex.singleFunctor A 0).map b, hb⟩
  constructor
  · intro a b hab
    have h : e.inv ≫ a ≫ e'.hom = e.inv ≫ b ≫ e'.hom := hs.1 (by
      simp only [Functor.map_comp, hab])
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
      Category.comp_id, Category.id_comp] using congrArg (fun k ↦ e.hom ≫ k ≫ e'.inv) h
  · intro a
    obtain ⟨b, hb⟩ := hs.2
      (DerivedCategory.Q.map e.inv ≫ a ≫ DerivedCategory.Q.map e'.hom)
    refine ⟨e.hom ≫ b ≫ e'.inv, ?_⟩
    apply (cancel_epi (DerivedCategory.Q.map e.inv)).1
    rw [← DerivedCategory.Q.map_comp, ← Category.assoc, e.inv_hom_id,
      Category.id_comp, Functor.map_comp, hb]
    simp only [Category.assoc]
    rw [← DerivedCategory.Q.map_comp, e'.hom_inv_id, CategoryTheory.Functor.map_id,
      Category.comp_id]

private theorem cofiberMap_eq_coneMap
    {V : Type*} [Category V] [Abelian V]
    {K L K' L' : CochainComplex V ℤ} (f : K ⟶ L) (g : K' ⟶ L')
    (a : K ⟶ K') (b : L ⟶ L') (h : a ≫ g = f ≫ b) :
    HomologicalComplex.homotopyCofiber.mapArrowHom f g
      (fun j ↦ ⟨j - 1, sub_add_cancel j 1⟩) (Arrow.homMk a b h) =
      CochainComplex.mappingCone.map f g a b h.symm := by
  ext i
  apply HomologicalComplex.homotopyCofiber.ext_from_X f (i + 1) i rfl
  all_goals simp [HomologicalComplex.homotopyCofiber.mapArrowHom,
    HomologicalComplex.homotopyCofiber.desc_f,
    HomologicalComplex.homotopyCofiber.inrCompHomotopy_hom,
    CochainComplex.mappingCone.map, CochainComplex.mappingCone.desc,
    CochainComplex.mappingCone.descCochain, CochainComplex.HomComplex.Cochain.comp_v,
    CochainComplex.mappingCone.inl, CochainComplex.mappingCone.fst,
    CochainComplex.mappingCone.snd, CochainComplex.mappingCone.inr]

private def generic_roos_bridge {A : Type*} [Category A] [Abelian A]
    [HasCountableProducts A] :
    HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
      integralOperationsRoosFunctor ≅ roosF (A := A) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro X Y f
    dsimp only [CategoryTheory.Functor.comp_map, NatTrans.id_app,
      Category.id_comp, Category.comp_id, Iso.refl_hom,
      integralOperationsRoosFunctor, integralOperationsRoosMap]
    rw [cofiberMap_eq_coneMap]
    simp only [Category.id_comp, Category.comp_id]
    rfl)

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem regular_presentation_support (Y : Scheme.{u})
    (C : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj C ≅
        ((scalarReductionExtension l E Y n).mapHomologicalComplex (.up ℤ)).obj
          (constantWeilIntegralGood l E Y).obj) :
    ∀ i : ℤ, i ≠ 0 → IsZero (C.X i) := by
  intro i hi
  have hz (n : ℕ) : IsZero ((coefficientSequenceEvaluation l E Y n).obj (C.X i)) := by
    have hP : IsZero ((constantWeilIntegralGood l E Y).obj.X i) :=
      HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ i hi
    exact ((scalarReductionExtension l E Y n).map_isZero hP).of_iso
      ((HomologicalComplex.eval _ _ i).mapIso (κ n))
  rw [IsZero.iff_id_eq_zero]
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  obtain ⟨⟨n, V⟩⟩ := V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have h := congrArg (fun k ↦ k.val.app (op V) x)
    ((hz n).eq_of_src (𝟙 _) 0)
  exact h

/-- Two primitive models at the regular representative give the same realization there.
Source: Stacks 0941 and 07A4; degree-zero regular quotient presentations.
(blueprint: lem-pur-completed-unit-regular-model-rigidity).

Proof: take the two strict presentations C and D supplied by the hypotheses.
Their finite isomorphisms with the quotient of the regular single complex assemble,
using the horizontal equations in CoefficientReductionPresentation, to a strict
isomorphism C ≅ D. Both complexes are concentrated in degree zero up to the
specified single-complex isomorphisms. The finite reduction equations identify
the two maps out of the reduction of the regular object after this isomorphism:
conjugate by either presentation, use full faithfulness of the degree-zero single
functor, then use sectionwise extensionality on the sequence site. This argument
uses no faithfulness for general derived evaluations. The prescribed component
formulas identify the two pulled strict tower comparisons under C ≅ D. Naturality
of exact pullback, restriction and the Roos comparison identifies the postcomposites
of the two realization components. Cancel the common comparison isomorphism.
All identifications are of entire strict towers, including the zero shifted
coordinate; the zero regular object on an empty scheme needs no separate choice. -/
theorem regularPullbackModel_rigid {X Y : Scheme.{u}} (f : X ⟶ Y)
    (ρ : PrimitiveCounit.RoosRealization l E X)
    (r s : integralDerivedPullback l E f ≅
      (calculus l E Y).reduction ⋙ PrimitiveCounit.pull l E f ⋙
        coefficientSequenceLimit l E X)
    (hr : regularPullbackModel l E f ρ r)
    (hs : regularPullbackModel l E f ρ s) :
    r.hom.app (integralConstantCoefficientObject l E Y) =
      s.hom.app (integralConstantCoefficientObject l E Y) := by
  obtain ⟨C, eC, κC, zC, hC, hzC, hr⟩ := hr
  obtain ⟨D, eD, κD, zD, hD, hzD, hs⟩ := hs
  have hCs := regular_presentation_support l E Y C κC
  have hDs := regular_presentation_support l E Y D κD
  obtain ⟨φ, hφ⟩ := (q_map_bijective_single_support C D hCs hDs).2
    (eC.inv ≫ eD.hom)
  have heφ : eC.hom ≫ DerivedCategory.Q.map φ = eD.hom := by
    rw [hφ, Iso.hom_inv_id_assoc]
  have hκ (n : ℕ) :
      ((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).map φ ≫
        (κD n).hom = (κC n).hom := by
    let V := coefficientSequenceEvaluation l E Y n
    let VC := V.mapHomologicalComplex (.up ℤ)
    have hVC (i : ℤ) (hi : i ≠ 0) : IsZero ((VC.obj C).X i) :=
      V.map_isZero (hCs i hi)
    have hP (i : ℤ) (hi : i ≠ 0) :
        IsZero ((((scalarReductionExtension l E Y n).mapHomologicalComplex (.up ℤ)).obj
          (constantWeilIntegralGood l E Y).obj).X i) :=
      (scalarReductionExtension l E Y n).map_isZero
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ i hi)
    apply (q_map_bijective_single_support _ _ hVC hP).1
    have hc := hC.1 n
    have hd := hD.1 n
    change CoefficientComparisonEquation _ _ _ _ _ at hc hd
    unfold CoefficientComparisonEquation at hc hd
    apply (cancel_epi
      ((coefficientSequenceDerivedEvaluation l E Y n).map eC.hom ≫
        V.mapDerivedCategoryFactors.hom.app C)).1
    simp only [Functor.map_comp, Category.assoc]
    rw [← V.mapDerivedCategoryFactors_hom_naturality_assoc,
      ← Functor.map_comp_assoc, heφ]
    exact hd.trans hc.symm
  let I := (PrimitiveCounit.inverse l E f).mapHomologicalComplex (.up ℤ)
  let R := PrimitiveCounit.restrictComplex l E X
  let F := HomologicalComplex.complexOfFunctorsToFunctorToComplex
    (T := ℕᵒᵖ) (V := scalarReductionSource l E X) (c := .up ℤ)
  let ψ := R.map (I.map φ)
  have hz : F.map ψ ≫ zD.hom = zC.hom := by
    apply NatTrans.ext
    funext n
    obtain ⟨n⟩ := n
    simp only [NatTrans.comp_app, hzD, hzC]
    have hrestrict := (NatIso.mapHomologicalComplex
      (eqToIso (coefficientSequenceRestriction_evaluation l E X n)) (.up ℤ)).hom.naturality
        (I.map φ)
    have hinverse := (PrimitiveCounit.inverseComplexEvaluation l E f n).hom.naturality φ
    dsimp only [Functor.comp_map] at hinverse
    change (F.map ψ).app (op n) ≫ (PrimitiveCounit.restrictEvaluation l E X _ n).hom =
      (PrimitiveCounit.restrictEvaluation l E X _ n).hom ≫
        ((scalarReductionRestriction l E X n).mapHomologicalComplex (.up ℤ)).map
          (((coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ)).map
            (I.map φ)) at hrestrict
    rw [← Category.assoc, hrestrict, Category.assoc, ← Functor.map_comp]
    congr 1
    rw [← Category.assoc, hinverse, Category.assoc, ← Functor.map_comp, hκ]
  have hpull :
      (PrimitiveCounit.pullRestrictionIso l E f
        (calculus l E Y).toCoefficientDerivedSystemReduction
        (constantWeilIntegralGood l E Y).obj C eC).hom ≫ DerivedCategory.Q.map ψ =
      (PrimitiveCounit.pullRestrictionIso l E f
        (calculus l E Y).toCoefficientDerivedSystemReduction
        (constantWeilIntegralGood l E Y).obj D eD).hom := by
    dsimp only [PrimitiveCounit.pullRestrictionIso, Iso.trans_hom, Functor.mapIso_hom,
      Iso.app_hom]
    rw [Category.assoc,
      ← (coefficientSequenceRestriction l E X).mapDerivedCategoryFactors_hom_naturality
        (I.map φ)]
    simp only [← Functor.map_comp, ← Category.assoc]
    congr 2
    rw [Category.assoc,
      ← (PrimitiveCounit.inverse l E f).mapDerivedCategoryFactors_hom_naturality φ]
    change (PrimitiveCounit.inverse l E f).mapDerivedCategory.map eC.hom ≫
        (PrimitiveCounit.inverse l E f).mapDerivedCategory.map (DerivedCategory.Q.map φ) ≫
          (PrimitiveCounit.inverse l E f).mapDerivedCategoryFactors.hom.app D =
      (PrimitiveCounit.inverse l E f).mapDerivedCategory.map eD.hom ≫
        (PrimitiveCounit.inverse l E f).mapDerivedCategoryFactors.hom.app D
    rw [← Functor.map_comp_assoc, heφ]
  have hbridge :
      integralOperationsRoosFunctor.map (F.map ψ) ≫
          (PrimitiveCounit.roosBridge l E X _).hom =
        (PrimitiveCounit.roosBridge l E X _).hom ≫ roosF.map ψ :=
    generic_roos_bridge.hom.naturality ψ
  have hz' : zC.inv ≫ F.map ψ = zD.inv := by
    apply (cancel_mono zD.hom).1
    rw [Category.assoc, hz, zC.inv_hom_id, zD.inv_hom_id]
  have hroos :
      DerivedCategory.Q.map (integralOperationsRoosFunctor.map zC.inv) ≫
          DerivedCategory.Q.map (PrimitiveCounit.roosBridge l E X _).hom ≫
          DerivedCategory.Q.map (roosF.map ψ) =
        DerivedCategory.Q.map (integralOperationsRoosFunctor.map zD.inv) ≫
          DerivedCategory.Q.map (PrimitiveCounit.roosBridge l E X _).hom := by
    have ht :
        integralOperationsRoosFunctor.map zC.inv ≫
            (PrimitiveCounit.roosBridge l E X _).hom ≫ roosF.map ψ =
          integralOperationsRoosFunctor.map zD.inv ≫
            (PrimitiveCounit.roosBridge l E X _).hom := by
      rw [← hbridge, ← Category.assoc, ← integralOperationsRoosFunctor.map_comp, hz']
    simpa only [Functor.map_comp] using congrArg DerivedCategory.Q.map ht
  have hn := (ρ.comparison.inv.naturality ψ).symm
  change ρ.comparison.inv.app _ ≫ DerivedCategory.Q.map (roosF.map ψ) =
    (coefficientConstantTowerLimit l E X).map (DerivedCategory.Q.map ψ) ≫
      ρ.comparison.inv.app _ at hn
  have h := congrArg (fun k ↦ k ≫ DerivedCategory.Q.map (roosF.map ψ)) hr
  simp only [Functor.mapIso_hom, Iso.symm_hom, Category.assoc] at h hs
  rw [hroos, hs, hn, ← (coefficientConstantTowerLimit l E X).map_comp_assoc,
    hpull] at h
  apply (cancel_mono
    ((coefficientConstantTowerLimit l E X).map
      (PrimitiveCounit.pullRestrictionIso l E f
        (calculus l E Y).toCoefficientDerivedSystemReduction
        (constantWeilIntegralGood l E Y).obj D eD).hom ≫ ρ.comparison.inv.app _)).1
  exact h.symm

end WeilConjectures.CompletedUnitPullback
