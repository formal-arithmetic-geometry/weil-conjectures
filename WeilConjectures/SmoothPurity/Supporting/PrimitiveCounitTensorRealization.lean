/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.PrimitiveCounit.PrimitiveCounitComparisonModels
import WeilConjectures.SmoothPurity.PrimitiveCounit.PrimitiveTensorStrictTowerComparison
import WeilConjectures.PoincareDuality.Pod.PodNativeRoosFunctorComparison
import all Mathlib.CategoryTheory.Limits.HasLimits

/-! # Tensor realization on strict quotient models

Source: Stacks Project, Tag 0941, lemma-derived-limit-is-ok, together with
strict quotient-system models and normalized Roos descent.
(blueprint: lem-pur-primitive-counit-tensor-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.hasDerived

attribute [local implicit_reducible] WeilConjectures.integralOperationsGoodLocalization
  WeilConjectures.integralOperationsTensorOnGood
  WeilConjectures.integralCompletedTensorComparison
  WeilConjectures.coefficientSequenceLimit
  WeilConjectures.PrimitiveCounit.RoosComparison
  WeilConjectures.integralOperationsTensorComplexFunctor
  WeilConjectures.integralOperationsRoosFunctor CategoryTheory.roosF

attribute [local irreducible] HasDerivedCategory.standard
attribute [local implicit_reducible] SheafOfModules.instAbelian
  CategoryTheory.abelianOfAdjunction CategoryTheory.Abelian.ofCoimageImageComparisonIsIso
  WeilConjectures.scalarReductionSourceDerived WeilConjectures.coefficientConstantTowerDerived
  WeilConjectures.integralOperationsCommHasDerivedCategory
  WeilConjectures.integralTowerHasDerivedCategory
  WeilConjectures.integralCompletedRingHasDerivedCategory

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

private theorem paste_five {A : Type*} [Category A]
    {V W X Y Z T : A} (f : V ⟶ W) (g : W ⟶ X) (h : X ⟶ Y)
    (i : Y ⟶ Z) (j : Z ⟶ T) :
    f ≫ (g ≫ (h ≫ i)) ≫ j = (f ≫ g) ≫ h ≫ i ≫ j := by
  simp only [Category.assoc]

private theorem cancel_presentation {A : Type*} [Category A]
    {V W X Y Z T : A} (d₁ : V ⟶ W) (d₂ : W ⟶ X) (d₃ : X ⟶ Z)
    (c : V ⟶ T) (b : Y ≅ Z) (e : Y ≅ T)
    (h : d₁ ≫ d₂ ≫ d₃ ≫ b.inv ≫ e.hom = c) :
    c ≫ e.inv ≫ b.hom = d₁ ≫ d₂ ≫ d₃ := by
  rw [← h]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id]

set_option maxHeartbeats 2000000 in
-- Normalize the derived tensor and strict Roos comparison instances.
/-- The completed tensor is the total limit of the tensor of coherent reductions,
with its prescribed comparison on every pair of good representatives.
Source: Stacks Tag 0941; steps 1--3 of the primitive comparison argument.
(blueprint: lem-pur-primitive-counit-tensor-realization).

Proof: choose functorial K-flat quotient representatives of reduction and their
strict tensor tower comparison, including its finite component equations. Tensor
the natural reduction comparisons and use the system tensor model. After applying
the coefficient limit, its restriction factorization, the inverse supplied Roos
comparison, the Roos bridge and the strict tower comparison give a natural
isomorphism on the product of good categories. Apply the universal property of
integralCompletedTensorDescent. Its factorization equation, composed with the
inverse strict tower comparison, is the required Roos equation. The presentation
and finite equations are those of the two input constructions. This argument
uses no faithfulness of finite derived evaluations, and does not need to construct
a new Roos descent. It includes zero inputs, empty schemes and level zero. -/
theorem primitiveCounitTensorRealization
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})
    (S : CoefficientDerivedSystemReduction l E W)
    (ρ : PrimitiveCounit.RoosRealization l E W) :
    ∃ r : integralCompletedTensor l E W ≅
      S.reduction.prod S.reduction ⋙ S.systemClosed.tensor ⋙ coefficientSequenceLimit l E W,
      PrimitiveCounit.TensorModel l E W S ρ r := by
  classical
  obtain ⟨M⟩ := PrimitiveCounit.reductionRepresentatives_nonempty l E W S
  obtain ⟨z, hz⟩ := PrimitiveCounit.tensorStrictTowerComparison l E W S M
  let L := coefficientSequenceLimit l E W
  let H := (integralOperationsRoosFunctor (A := scalarReductionSource l E W)) ⋙
    DerivedCategory.Q
  let B := M.complexes.prod M.complexes ⋙
    coefficientTotalTensor.{u, t + 1, t}
      (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W)
  let k := ObjectProperty.lift (CochainComplex.IsKFlatIndependentCoefficients
    (J := coefficientSequenceTopology (Scheme.ProEt.topology W))
    (R := coefficientSequenceCommRingSheaf l E W) :
      ObjectProperty (CochainComplex (coefficientSequenceModules l E W) ℤ))
        M.complexes M.good
  let c : ((integralOperationsGoodLocalization l E W).prod
      (integralOperationsGoodLocalization l E W)) ⋙
      (S.reduction.prod S.reduction ⋙ S.systemClosed.tensor) ≅ B ⋙ DerivedCategory.Q :=
    Functor.isoWhiskerRight (NatIso.prod M.comparison M.comparison) S.systemClosed.tensor ≪≫
      Functor.isoWhiskerLeft (k.prod k) S.systemTensorModel.comparison.symm
  let ν : DerivedCategory.Q ⋙ coefficientConstantTowerLimit l E W ≅
      HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙ H :=
    ρ.comparison.symm ≪≫
      Functor.isoWhiskerRight (podNativeRoosIso (A := scalarReductionSource l E W)).symm
        DerivedCategory.Q
  let η : DerivedCategory.Q ⋙ L ≅
      PrimitiveCounit.restrictComplex l E W ⋙
        HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙ H :=
    Functor.isoWhiskerRight (coefficientSequenceRestriction l E W).mapDerivedCategoryFactors
        (coefficientConstantTowerLimit l E W) ≪≫
      Functor.isoWhiskerLeft (PrimitiveCounit.restrictComplex l E W) ν
  let δ : ((integralOperationsGoodLocalization l E W).prod
      (integralOperationsGoodLocalization l E W)) ⋙
      (S.reduction.prod S.reduction ⋙ S.systemClosed.tensor ⋙ L) ≅
      integralOperationsTensorOnGood l E W :=
    Functor.isoWhiskerRight c L ≪≫ Functor.isoWhiskerLeft B η ≪≫
      Functor.isoWhiskerRight z H
  obtain ⟨r, hr, _⟩ := (integralCompletedTensorDescent l E W).universal _ δ
  refine ⟨r, ?_⟩
  unfold PrimitiveCounit.TensorModel
  intro P Q
  let C := M.complexes.obj P
  let D := M.complexes.obj Q
  let eC := M.comparison.app P
  let eD := M.comparison.app Q
  let q := z.app (P, Q)
  refine ⟨C, D, M.good P, M.good Q, eC, eD,
    (fun n ↦ (M.evaluation n).app P), (fun n ↦ (M.evaluation n).app Q), q,
    M.presentation P, M.presentation Q, hz P Q, ?_⟩
  have he := congrArg (fun i ↦ i.hom.app (P, Q)) hr
  let a := (PrimitiveCounit.tensorRestrictionIso l E W S P.obj Q.obj
    C D (M.good P) (M.good Q) eC eD).hom
  let b := DerivedCategory.Q.mapIso
    (PrimitiveCounit.roosBridge l E W ((PrimitiveCounit.restrictComplex l E W).obj
      ((coefficientTotalTensor.{u, t + 1, t}
        (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W)).obj (C, D))))
  have ha : (coefficientConstantTowerLimit l E W).map a =
      L.map (c.hom.app (P, Q)) ≫
        (coefficientConstantTowerLimit l E W).map
          ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.hom.app
            (B.obj (P, Q))) := by
    change (coefficientConstantTowerLimit l E W).map
      ((coefficientSequenceDerivedRestriction l E W).map (c.hom.app (P, Q)) ≫
        (coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.hom.app
          (B.obj (P, Q))) = _
    exact (coefficientConstantTowerLimit l E W).map_comp _ _
  have hδ : δ.hom.app (P, Q) =
      (coefficientConstantTowerLimit l E W).map a ≫
        ρ.comparison.inv.app _ ≫ b.inv ≫ H.map q.hom := by
    change L.map (c.hom.app (P, Q)) ≫
      ((coefficientConstantTowerLimit l E W).map
        ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.hom.app
          (B.obj (P, Q))) ≫
        (ρ.comparison.inv.app _ ≫ DerivedCategory.Q.map (𝟙 _))) ≫
      H.map q.hom = _
    rw [ha]
    change L.map (c.hom.app (P, Q)) ≫
      ((coefficientConstantTowerLimit l E W).map
        ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.hom.app
          (B.obj (P, Q))) ≫ (ρ.comparison.inv.app _ ≫ b.inv)) ≫ H.map q.hom = _
    exact paste_five _ _ _ _ _
  have he' : r.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
      (coefficientConstantTowerLimit l E W).map a ≫
        ρ.comparison.inv.app _ ≫ b.inv ≫ H.map q.hom =
      (integralCompletedTensorComparison l E W).hom.app (P, Q) := by
    change r.hom.app _ ≫ _ = _ at he
    rw [hδ] at he
    simpa only [Category.assoc, integralCompletedTensorComparison,
      Functor.prod_obj, integralOperationsGoodLocalization, Functor.comp_obj,
      ObjectProperty.ι_obj, integralOperationsTensorOnGood,
      integralOperationsTensorComplexFunctor, H] using he
  change (integralCompletedTensorComparison l E W).hom.app (P, Q) ≫
      (H.mapIso (z.app (P, Q))).inv ≫ b.hom =
    r.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
      (coefficientConstantTowerLimit l E W).map a ≫ ρ.comparison.inv.app _
  exact cancel_presentation _ _ _ _ b (H.mapIso (z.app (P, Q))) he'

end WeilConjectures
