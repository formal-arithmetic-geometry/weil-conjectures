/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedUnitPullback.CompletedUnitRegularModelData
import WeilConjectures.SmoothPurity.CompletedUnitPullback.CompletedUnitRoosNormalization
import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedQuotientReductionPresentation
import all WeilConjectures.SmoothPurity.CompletedUnitPullback.CompletedUnitSystemPullbackComparison

/-! # The canonical Roos realization at the regular representative -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.CompletedUnitPullback

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

attribute [local implicit_reducible] Functor.mapHomologicalComplex
  HomologicalComplex.asFunctor integralOperationsGoodLocalization
  integralOperationsPullbackOnGood integralOperationsPullbackTowerFunctor
  integralOperationsPullbackLevel integralOperationsRestrict
  Functor.ofOpSequence Functor.ofSequence

private theorem sectionwise_eqToIso
    {A D : Type*} [Category A] [Category D] (J : GrothendieckTopology D)
    (R : Sheaf J RingCat) (F G : A ⥤ SheafOfModules R) (h : F = G) (δ : F ≅ G)
    (hδ : ∀ (M : A) (U : D) (x : (F.obj M).val.obj (op U)),
      HEq ((δ.hom.app M).val.app (op U) x) x) : δ = eqToIso h := by
  subst G
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply SheafOfModules.hom_ext
  ext U x
  exact eq_of_heq (hδ M U.unop x)

private theorem eqToIso_trans_heq
    {A : Type*} [Category A] {X Y Z : A} (h : X = Y) (h' : Y = Z) :
    HEq (eqToIso (h.trans h')) (eqToIso h') := by
  subst Y
  rfl

private theorem directEvaluation_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    HEq (pullbackTensorSequenceDirectEvaluation l E f n)
      (eqToIso (PrimitiveCounit.directEvaluation_eq l E f n)) := by
  have hd : pullbackTensorSequenceDirect l E f = PrimitiveCounit.direct l E f := by
    unfold pullbackTensorSequenceDirect PrimitiveCounit.direct
    simp only [ring_eq l E f]
  have h := (pullbackTensorSequenceDirectEvaluation_existsUnique l E f n).exists.choose_spec
  have he := sectionwise_eqToIso (Scheme.ProEt.topology Y) (integralCoefficientSheaf l E Y n)
    _ _ ((congrArg (· ⋙ coefficientSequenceEvaluation l E Y n) hd).trans
      (PrimitiveCounit.directEvaluation_eq l E f n))
    (pullbackTensorSequenceDirectEvaluation l E f n) h
  exact (heq_of_eq he).trans (eqToIso_trans_heq
    (congrArg (· ⋙ coefficientSequenceEvaluation l E Y n) hd)
    (PrimitiveCounit.directEvaluation_eq l E f n))

private theorem inverse_mates_heq
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (G G' : B ⥤ A) [G.IsRightAdjoint] [G'.IsRightAdjoint] (hG : G = G')
    (U : A ⥤ C) (V : B ⥤ D) {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    (d : G ⋙ U ≅ V ⋙ R) (d' : G' ⋙ U ≅ V ⋙ R) (hd : HEq d d')
    (e : U ⋙ L ≅ G.leftAdjoint ⋙ V) (e' : G'.leftAdjoint ⋙ V ≅ U ⋙ L)
    (he : ∀ M, adj.homEquiv _ _ (e.hom.app M) =
      U.map ((Adjunction.ofIsRightAdjoint G).unit.app M) ≫ d.hom.app _)
    (he' : ∀ M, U.map ((Adjunction.ofIsRightAdjoint G').unit.app M) ≫
      d'.hom.app _ ≫ R.map (e'.hom.app M) = adj.unit.app (U.obj M)) :
    HEq e.symm e' := by
  subst G'
  have hd' : d = d' := eq_of_heq hd
  subst d'
  apply heq_of_eq
  have hi : e = e'.symm := by
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply (adj.homEquiv _ _).injective
    rw [he M, Adjunction.homEquiv_unit, ← he' M]
    simp only [Category.assoc, ← R.map_comp, Iso.symm_hom, Iso.hom_inv_id_app,
      ]
    erw [R.map_id, Category.comp_id]
  exact congrArg Iso.symm hi

attribute [local irreducible] Functor.leftAdjoint PrimitiveCounit.inverseEvaluation
  coefficientSequenceCommRingSheaf coefficientSequenceCommRingPresheaf

set_option maxHeartbeats 1600000 in
-- Comparing the chosen adjunctions retains the full coefficient-system instances.
attribute [local irreducible] coefficientSequenceEvaluation
  Scheme.coefficientProEtaleModuleDirectImage in
private theorem inverseEvaluation_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    HEq (pullbackTensorSequenceInverseEvaluation l E f n).symm
      (PrimitiveCounit.inverseEvaluation l E f n) := by
  have hd : pullbackTensorSequenceDirect l E f = PrimitiveCounit.direct l E f := by
    unfold pullbackTensorSequenceDirect PrimitiveCounit.direct
    simp only [ring_eq l E f]
  exact inverse_mates_heq _ _ hd
    (coefficientSequenceEvaluation l E Y n) (coefficientSequenceEvaluation l E X n)
    (Scheme.coefficientProEtaleModuleAdjunction.{u, u} f
      (CommRingCat.of (ULift.{u + 1} (finiteCoefficientRing l E (n + 1)))))
    _ _ (directEvaluation_eq l E f n) _ _
    (pullbackTensorSequenceInverseEvaluation_existsUnique l E f n).exists.choose_spec
    (by
      intro M
      unfold PrimitiveCounit.inverseEvaluation
      exact (PrimitiveCounit.inverseEvaluation_existsUnique l E f n).choose_spec.1 M)

private theorem mapComplex_congr
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    (F G : A ⥤ B) [F.Additive] [G.Additive] (h : F = G) :
    F.mapHomologicalComplex (.up ℤ) = G.mapHomologicalComplex (.up ℤ) := by
  subst G
  rfl

private theorem finite_reference_transport
    {A B C D W : Type*} [Category A] [Category B] [Category C] [Category D]
    [Category W] (F G : A ⥤ B) (h : F = G)
    (U : A ⥤ C) (V : B ⥤ D) (L : C ⥤ D)
    (e : U ⋙ L ≅ F ⋙ V) (e' : G ⋙ V ≅ U ⋙ L) (he : HEq e.symm e')
    (R : D ⥤ W) (S : B ⥤ W) (r : S ≅ V ⋙ R)
    (M : A) (N : C) (k : U.obj M ⟶ N) :
    HEq ((𝟙 _ ≫ r.hom.app (F.obj M) ≫ 𝟙 _) ≫ R.map (𝟙 _) ≫
        R.map (e.inv.app M) ≫ R.map (𝟙 _) ≫ R.map (L.map k))
      (r.hom.app (G.obj M) ≫ R.map (𝟙 _) ≫
        R.map (e'.hom.app M) ≫ R.map (𝟙 _) ≫ R.map (L.map k)) := by
  subst G
  have he' : e.symm = e' := eq_of_heq he
  subst e'
  simp only [Iso.symm_hom, R.map_id, Category.id_comp, Category.comp_id, heq_eq_eq]

private theorem derived_reference_transport
    {A B D : Type*} [Category A] [Category B] [Category D]
    [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
    (F G : A ⥤ B) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (h : F = G) (h' : F.mapDerivedCategory = G.mapDerivedCategory)
    (R : DerivedCategory B ⥤ D) (T : CochainComplex B ℤ ⥤ D)
    (β : ∀ C, R.obj (DerivedCategory.Q.obj C) ≅ T.obj C)
    (K : DerivedCategory A) (C : CochainComplex A ℤ) (e : K ≅ DerivedCategory.Q.obj C) :
    R.map (F.mapDerivedCategory.map e.hom) ≫
        R.map (F.mapDerivedCategoryFactors.hom.app C) ≫
        (β ((F.mapHomologicalComplex (.up ℤ)).obj C)).hom ≫
        T.map (eqToHom (congrArg (fun J ↦ J.obj C) (mapComplex_congr F G h))) =
      R.map (eqToHom (congrArg (fun J ↦ J.obj K) h')) ≫
        R.map (G.mapDerivedCategory.map e.hom) ≫
        R.map (G.mapDerivedCategoryFactors.hom.app C) ≫
        (β ((G.mapHomologicalComplex (.up ℤ)).obj C)).hom := by
  subst G
  simp only [eqToHom_refl]
  rw [T.map_id, R.map_id]
  simp only [Category.id_comp, Category.comp_id]

private theorem complex_hom_heq
    {A : Type*} [Category A] [HasZeroMorphisms A]
    {K K' L L' : CochainComplex A ℤ} (hK : K = K') (hL : L = L')
    {a : K ⟶ L} {b : K' ⟶ L'} (h : ∀ i : ℤ, HEq (a.f i) (b.f i)) : HEq a b := by
  subst K'
  subst L'
  apply heq_of_eq
  ext i
  exact eq_of_heq (h i)

set_option maxHeartbeats 1600000 in
-- The composite comparison retains the chosen derived-category and sheaf instances.
/-- The tensor pullback realization has the primitive regular representative model.
Source: Stacks 0941, 099N and 07A4; the normalized ordinary reduction/limit adjunction.
(blueprint: lem-pur-completed-unit-canonical-regular-model).

Proof: use the ordinary reduction of the good regular single complex as C, the
adjunction-normalized pullbackTensorReductionModel as eC, and the inverse ordinary
finite reduction comparisons as κC. The theorem
completedQuotientReductionPresentation supplies their finite and horizontal
equations: its proof transposes under the finite adjunction and uses the unit
projection equations to identify both sides with the quotient unit.
Identify the two sequence inverse images by their ring-map equality. Their finite
inverse-image comparisons have equal transposes under these same adjunctions, so
they agree. Use pullbackTensorPullbackTower for z and these equalities for its
prescribed components. Expand the defining component of the canonical integral
pullback realization at the regular good complex. Its comparison is the composite
of the reduction model, exact inverse-image factorization, the total-limit/Roos
model and this strict tower isomorphism. The proved theorem primitive_roos_inverse_eq
identifies the two Roos comparisons
on every complex through the strict bridge. Its proof uses the resolution equation
on K-injectives and equality of both shifted-cone coordinates, then naturality.
This identifies the
composite with pullRestrictionIso followed by ρ.comparison.inv.
Cancellation gives precisely the displayed regular model equation, on the entire
strict tower and both Roos coordinates. No finite derived faithfulness is used. -/
theorem tensorPrimitiveRealization_regularModel {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (ρ : PrimitiveCounit.RoosRealization l E X) :
    regularPullbackModel l E f ρ (tensorPrimitiveRealization l E f) := by
  let P := constantWeilIntegralGood l E Y
  let C := ((pullbackTensorOrdinaryReduction l E Y).mapHomologicalComplex (.up ℤ)).obj P.obj
  let eC := (pullbackTensorReductionModel l E Y).app P
  let κC := fun n ↦ ((pullbackTensorReductionEvaluationComplex l E Y n).app P.obj).symm
  let D := ((PrimitiveCounit.inverse l E f).mapHomologicalComplex (.up ℤ)).obj C
  let Z := ((PrimitiveCounit.restrictComplex l E X).obj D)
  have hI := inverse_eq l E f
  have hDC : (((pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ)).obj C) =
      D := by
    exact congrArg (fun J ↦ J.obj C) (mapComplex_congr _ _ hI)
  let z : Z.asFunctor ≅ (integralOperationsPullbackTowerFunctor l E f).obj P.obj :=
    eqToIso (congrArg (fun K ↦
      ((PrimitiveCounit.restrictComplex l E X).obj K).asFunctor) hDC.symm) ≪≫
        pullbackTensorPullbackTower l E f P.obj
  refine ⟨C, eC, κC, z, ?_, ?_, ?_⟩
  · exact CompletedQuotient.completedQuotientReductionPresentation l E Y P
  · intro n
    have hn := (pullbackTensorPullbackTower_existsUnique l E f P.obj).exists.choose_spec n
    change (pullbackTensorPullbackTower l E f P.obj).app (op n) = _ at hn
    have hh := congrArg Iso.hom hn
    dsimp only [Iso.app_hom] at hh
    dsimp only [z, Iso.trans_hom, NatTrans.comp_app, eqToIso.hom]
    rw [hh]
    apply eq_of_heq
    simp only [eqToHom_app, eqToHom_comp_heq_iff]
    simp only [pullbackTensorPullbackTowerLevel, Iso.trans_hom,
      Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv]
    apply complex_hom_heq
      (congrArg (fun K ↦ ((PrimitiveCounit.restrictComplex l E X).obj K).asFunctor.obj
        (op n)) hDC) rfl
    intro i
    have h := finite_reference_transport
      (pullbackTensorSequenceInverse l E f) (PrimitiveCounit.inverse l E f) hI
      (coefficientSequenceEvaluation l E Y n) (coefficientSequenceEvaluation l E X n)
      (integralOperationsLevelPullback l E f n)
      (pullbackTensorSequenceInverseEvaluation l E f n)
      (PrimitiveCounit.inverseEvaluation l E f n) (inverseEvaluation_eq l E f n)
      (scalarReductionRestriction l E X n)
      (coefficientSequenceRestriction l E X ⋙
        (evaluation ℕᵒᵖ (integralTowerModules l E X)).obj (op n))
      (eqToIso (coefficientSequenceRestriction_evaluation l E X n))
      (C.X i) _ ((κC n).hom.f i)
    dsimp only [C, D, Z] at h ⊢
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      pullbackTensorRestrictedLevel, PrimitiveCounit.restrictEvaluation,
      pullbackTensorInverseEvaluationComplex, PrimitiveCounit.inverseComplexEvaluation,
      Iso.trans_hom, Iso.trans_inv, Iso.app_hom, Iso.app_inv, Iso.symm_hom, Iso.symm_inv,
      Functor.mapHomologicalComplexCompIso_hom_app_f,
      Functor.mapHomologicalComplexCompIso_inv_app_f,
      NatIso.mapHomologicalComplex_hom_app_f, NatIso.mapHomologicalComplex_inv_app_f,
      Iso.refl_hom, Iso.refl_inv, NatTrans.comp_app, NatTrans.id_app,
      Functor.map_comp, Category.assoc]
    simpa only [κC, Iso.symm_hom, Iso.app_inv, Functor.comp_obj,
      Functor.mapHomologicalComplex_obj_X, Category.assoc] using h
  · let R := coefficientSequenceLimit l E X
    let H := integralOperationsRoosFunctor (A := scalarReductionSource l E X) ⋙ DerivedCategory.Q
    have hc := (pullbackTensorIntegralPullbackModel_existsUnique l E f).exists.choose_spec P
    change (pullbackTensorIntegralPullbackModel l E f).app
      (DerivedCategory.Q.obj P.obj) = _ at hc
    have hc' : (pullbackTensorIntegralPullbackModel l E f).app
          (DerivedCategory.Q.obj P.obj) ≪≫ pullbackTensorReferencePullbackModel l E f P =
        (integralDerivedPullbackComparison l E f).app P := by
      rw [hc]
      simp only [Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl]
    have hf := congrArg Iso.hom hc'
    change (pullbackTensorIntegralPullbackModel l E f).hom.app _ ≫
      R.map ((pullbackTensorSequenceDerived l E f).map eC.hom) ≫
      R.map ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app C) ≫
      (pullbackTensorLimitRoos l E X _).hom ≫
      H.map (pullbackTensorPullbackTower l E f P.obj).hom = _ at hf
    rw [tensorPrimitiveRealization_hom, primitive_roos_inverse_eq]
    simp only [Iso.app_hom] at hf
    erw [← hf]
    simp only [Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
    change (pullbackTensorIntegralPullbackModel l E f).hom.app
        (DerivedCategory.Q.obj P.obj) ≫
      R.map ((pullbackTensorSequenceDerived l E f).map eC.hom) ≫
      R.map ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app C) ≫
      (pullbackTensorLimitRoos l E X _).hom ≫
      H.map (pullbackTensorPullbackTower l E f P.obj).hom ≫ H.map z.inv ≫
      DerivedCategory.Q.map (PrimitiveCounit.roosBridge l E X Z).hom = _
    simp only [z, Iso.trans_inv, eqToIso.inv, H.map_comp, Category.assoc,
      Iso.map_hom_inv_id_assoc]
    let T := PrimitiveCounit.restrictComplex l E X ⋙
      HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙ H
    have ht := derived_reference_transport
      (pullbackTensorSequenceInverse l E f) (PrimitiveCounit.inverse l E f)
      hI (systemPullback_eq l E f) R T (pullbackTensorLimitRoos l E X)
      ((calculus l E Y).reduction.obj (DerivedCategory.Q.obj P.obj)) C eC
    have h := congrArg (fun a ↦
      (pullbackTensorIntegralPullbackModel l E f).hom.app
        (DerivedCategory.Q.obj P.obj) ≫ a ≫
      DerivedCategory.Q.map (PrimitiveCounit.roosBridge l E X Z).hom) ht
    simpa only [T, H, R, PrimitiveCounit.pullRestrictionIso, pullbackTensorLimitRoos,
      Functor.mapIso_hom, Iso.trans_hom, Iso.app_hom, Functor.map_comp,
      coefficientSequenceLimit, Functor.comp_map, eqToHom_map, Category.assoc,
      pullbackTensorSequenceDerived, PrimitiveCounit.pull, PrimitiveCounit.restrictComplex] using h

end WeilConjectures.CompletedUnitPullback
