/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.Paper.PointFibreDerivedTensorModels
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Sheaf.Paper.PointSheafHomMaps
import all Sheaf.Paper.IntegralAmbientOperationModels

/-! # The chain augmentation for integral point tensors

Source: Stacks 07A4 and 0941.
(blueprint: lem-sf-point-integral-tensor-chain).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] SheafOfModules.cochainModulesMonoidal
  SheafOfModules.cochainModulesSymmetric SheafOfModules.cochainModulesPreadditive
  SheafOfModules.cochainTensorLocalizationIsMonoidal
  SheafOfModules.cochainTensorLeftPreservesColimits
  SheafOfModules.cochainTensorRightPreservesColimits
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme Opposite
open scoped TensorProduct ChangeOfRings
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private def pointBeta
    (P Q : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :
    (pointIntegralComplexSections D l E).obj P ⊗
        (pointIntegralComplexSections D l E).obj Q ⟶
      (pointIntegralComplexSections D l E).obj
        ((coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology (Spec (.of D.k)))
          (completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k)))).obj (P, Q)) :=
  PointDerivedHom.SectionsTensorConstruction.chain.{u, u} D.k
    (completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k)))
    (PointDerivedHom.coefficientMap.{u, u} D.k l E 1 true) P Q

attribute [local irreducible] pointBeta
  completedIntegralCommRingSheafUnrestricted
  IntegralAmbient.tensorOperationUnit IntegralAmbient.tensorTowerIso
  IntegralOnSlice.augmentation

private theorem completion_first :
    PointIntegralTensorFirst D l E (fun P Q ↦ pointBeta D l E P.obj Q.obj ≫
      (pointIntegralComplexSections D l E).map
        (IntegralAmbient.tensorOperationUnit l E (Spec (.of D.k)) P.obj Q.obj)) := by
  intro P Q n p q x y
  let V := op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k))))
  let A := (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology (Spec (.of D.k)))
    (completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k)))).obj (P.obj, Q.obj)
  have hc := congrArg (fun f ↦ f ≫ Pi.π _ n)
    (IntegralAmbient.tensorOperationUnit_coordinates l E (Spec (.of D.k)) P.obj Q.obj).1
  simp only [Category.assoc, Pi.map_π, IntegralOnSlice.productAugmentation,
    Pi.lift_π_assoc] at hc
  change (((IntegralAmbient.tensorOperationUnit l E (Spec (.of D.k)) P.obj Q.obj ≫
    CochainComplex.mappingCocone.fst (pointTensorRoosEndomorphism D l E P.obj Q.obj) ≫
    Pi.π _ n).f (p + q)).val.app V
    (((pointBeta D l E P.obj Q.obj).f (p + q))
      (PointDerivedHom.moduleTotalElement _ _ p q x y))) = _
  unfold pointTensorRoosEndomorphism
  erw [hc]
  let d := ((IntegralAmbient.tensorTowerIso l E (Spec (.of D.k))).hom.app
    (P.obj, Q.obj)).app (op n)
  let γ := ((IntegralOnSlice.augmentation l E (Spec (.of D.k)) none).app A).app (op n)
  change (d.f (p + q)).val.app V
    ((γ.f (p + q)).val.app V
      ((pointBeta D l E P.obj Q.obj).f (p + q)
        (PointDerivedHom.moduleTotalElement _ _ p q x y))) = _
  rw [show ((pointBeta D l E P.obj Q.obj).f (p + q))
    (PointDerivedHom.moduleTotalElement _ _ p q x y) =
      PointDerivedHom.totalElement.{u, u} D.k
        (completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k)))
        P.obj Q.obj p q V x y from by
    unfold pointBeta
    with_unfolding_all
      exact PointDerivedHom.SectionsTensorConstruction.chain_apply D.k
        (completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k)))
        (PointDerivedHom.coefficientMap.{u, u} D.k l E 1 true) P.obj Q.obj p q x y]
  dsimp only [γ]
  unfold IntegralOnSlice.augmentation
  erw [(IntegralOnSlice.augmentation_existsUnique l E (Spec (.of D.k)) none).exists.choose_spec]
  have hn := (IntegralAmbient.tensorTowerModel l E (Spec (.of D.k))).exists.choose_spec
    P.obj Q.obj n p q V 1 x y
  simp only [d, IntegralAmbient.tensorTowerIso, A, V,
    PointDerivedHom.totalElement, IntegralHom.totalPair, IntegralHom.pair,
    coefficientTensorGenerator, IntegralHom.ordinaryTensor, CochainComplex.ιMapBifunctor] at hn ⊢
  exact hn

private theorem completion_second :
    PointIntegralTensorSecond D l E (fun P Q ↦ pointBeta D l E P.obj Q.obj ≫
      (pointIntegralComplexSections D l E).map
        (IntegralAmbient.tensorOperationUnit l E (Spec (.of D.k)) P.obj Q.obj)) := by
  intro P Q k z
  have h := (IntegralAmbient.tensorOperationUnit_coordinates l E (Spec (.of D.k))
    P.obj Q.obj).2 k (k + -1) rfl
  have hs := congrArg (fun f ↦ (pointIntegralSections l E D.k).map f) h
  rw [Functor.map_comp, Functor.map_zero] at hs
  have he := congrArg (fun f ↦ f ((pointBeta D l E P.obj Q.obj).f k z)) hs
  simp only [HomologicalComplex.comp_f, pointIntegralComplexSections,
    Functor.mapHomologicalComplex_map_f,
    ModuleCat.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply,
    pointTensorRoosEndomorphism] at he ⊢
  exact he

/-- The sections tensor map followed by the normalized sheaf Roos augmentation.
Source: Stacks 07A4 and 0941 (blueprint: lem-sf-point-integral-tensor-chain).
Proof: apply the ordinary sections tensor map and then tensorOperationUnit. Its
first coordinate is the normalized finite quotient tensor generator by
tensorTowerModel and augmentation_existsUnique. Its shifted coordinate vanishes
by tensorOperationUnit_coordinates, preserved by additive sections. -/
theorem pointIntegralTensorChain :
    ∃ completion : pointIntegralTensorCompletion D l E,
      PointIntegralTensorFirst D l E completion ∧
        PointIntegralTensorSecond D l E completion := by
  exact ⟨fun P Q ↦ pointBeta D l E P.obj Q.obj ≫
    (pointIntegralComplexSections D l E).map
      (IntegralAmbient.tensorOperationUnit l E (Spec (.of D.k)) P.obj Q.obj),
    completion_first D l E, completion_second D l E⟩

end WeilConjectures
