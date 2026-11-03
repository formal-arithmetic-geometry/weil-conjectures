/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedUnitPullback.CompletedUnitTensorSystemData
public import WeilConjectures.SmoothPurity.CompletedUnitPullback.CompletedUnitSystemPullbackComparison
public import WeilConjectures.SmoothPurity.Supporting.ConstantWeilStructure

/-! # The normalized pullback model at the regular good representative -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.CompletedUnitPullback

private theorem whiskered_equality_hom
    {C D A B : Type*} [Category C] [Category D] [Category A] [Category B]
    (R : C ⥤ D) (H G : D ⥤ A) (L : A ⥤ B) (F : C ⥤ B)
    (α : F ≅ R ⋙ H ⋙ L) (h : H = G) (K : C) :
    (α ≪≫ Functor.isoWhiskerLeft R
      (Functor.isoWhiskerRight (eqToIso h) L)).hom.app K =
      α.hom.app K ≫ L.map (eqToHom (congrArg (fun J ↦ J.obj (R.obj K)) h)) := by
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    eqToIso.hom, eqToHom_app]

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The strict primitive pullback model at the regular degree-zero representative.
Source: Stacks 0941; the regular specialization of PrimitiveCounit.PullModel.
(blueprint: def-pur-completed-unit-regular-model).
This retains the entire strict quotient tower and both Roos coordinates. -/
def regularPullbackModel {X Y : Scheme.{u}} (f : X ⟶ Y)
    (ρ : PrimitiveCounit.RoosRealization l E X)
    (r : integralDerivedPullback l E f ≅
      (calculus l E Y).reduction ⋙ PrimitiveCounit.pull l E f ⋙
        coefficientSequenceLimit l E X) : Prop :=
  let P := constantWeilIntegralGood l E Y;
    ∃ (C : CochainComplex (coefficientSequenceModules l E Y) ℤ)
      (eC : (calculus l E Y).reduction.obj (DerivedCategory.Q.obj P.obj) ≅
        DerivedCategory.Q.obj C)
      (κC : ∀ n : ℕ,
        ((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj C ≅
          ((scalarReductionExtension l E Y n).mapHomologicalComplex (.up ℤ)).obj P.obj)
      (z : ((PrimitiveCounit.restrictComplex l E X).obj
        (((PrimitiveCounit.inverse l E f).mapHomologicalComplex (.up ℤ)).obj C)).asFunctor ≅
          (integralOperationsPullbackTowerFunctor l E f).obj P.obj),
      CoefficientReductionPresentation l E Y
        (calculus l E Y).toCoefficientDerivedSystemReduction P.obj P.property.1 C eC κC ∧
      (∀ n : ℕ, z.hom.app (op n) =
        (PrimitiveCounit.restrictEvaluation l E X _ n).hom ≫
          ((scalarReductionRestriction l E X n).mapHomologicalComplex (.up ℤ)).map
            ((PrimitiveCounit.inverseComplexEvaluation l E f n).hom.app C ≫
              ((integralOperationsLevelPullback l E f n).mapHomologicalComplex (.up ℤ)).map
                (κC n).hom)) ∧
      (integralDerivedPullbackComparison l E f).hom.app P ≫
          DerivedCategory.Q.map (integralOperationsRoosFunctor.mapIso z.symm).hom ≫
          DerivedCategory.Q.map (PrimitiveCounit.roosBridge l E X _).hom =
        r.hom.app (DerivedCategory.Q.obj P.obj) ≫
          (coefficientConstantTowerLimit l E X).map
            (PrimitiveCounit.pullRestrictionIso l E f
              (calculus l E Y).toCoefficientDerivedSystemReduction P.obj C eC).hom ≫
          ρ.comparison.inv.app _

/-- The canonical tensor realization in primitive sequence-pullback coordinates.
Source: Stacks 0941; equality of the two normalized sequence inverse images.
(blueprint: def-pur-completed-unit-regular-model). -/
def tensorPrimitiveRealization {X Y : Scheme.{u}} (f : X ⟶ Y) :
    integralDerivedPullback l E f ≅
      (calculus l E Y).reduction ⋙ PrimitiveCounit.pull l E f ⋙
        coefficientSequenceLimit l E X :=
  pullbackTensorIntegralPullbackModel l E f ≪≫
    Functor.isoWhiskerLeft (calculus l E Y).reduction
      (Functor.isoWhiskerRight (eqToIso (systemPullback_eq l E f))
        (coefficientSequenceLimit l E X))

attribute [local irreducible] pullbackTensorIntegralPullbackModel

/-- The change of coordinates is the image of the equality of system pullbacks.
Source: functoriality of eqToHom.
(blueprint: def-pur-completed-unit-regular-model).
Proof: the component of the equality isomorphism is eqToHom of the object equality;
functors preserve equality morphisms. -/
theorem tensorPrimitiveRealization_hom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (scalarReductionSource l E Y)) :
    (tensorPrimitiveRealization l E f).hom.app K =
      (pullbackTensorIntegralPullbackModel l E f).hom.app K ≫
        (coefficientSequenceLimit l E X).map
          (eqToHom (congrArg (fun H ↦ H.obj ((calculus l E Y).reduction.obj K))
            (systemPullback_eq l E f))) := by
  exact whiskered_equality_hom (calculus l E Y).reduction
    (pullbackTensorSequenceDerived l E f) (PrimitiveCounit.pull l E f)
    (coefficientSequenceLimit l E X) (integralDerivedPullback l E f)
    (pullbackTensorIntegralPullbackModel l E f) (systemPullback_eq l E f) K

end WeilConjectures.CompletedUnitPullback
