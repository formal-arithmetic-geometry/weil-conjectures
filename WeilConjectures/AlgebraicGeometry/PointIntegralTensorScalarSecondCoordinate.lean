/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PointIntegralTensorScalarFirstCoordinate
import all WeilConjectures.AlgebraicGeometry.IntegralOperationsScalarComparisonModels
import all WeilConjectures.AlgebraicGeometry.ScalarRoosComparison
import all WeilConjectures.AlgebraicGeometry.ScalarExtensionComposition

/-! Shifted coordinate normalization for the point scalar square.

Source: Stacks 07A4 and 0941.
(blueprint: new-lem-sf-point-integral-tensor-scalar-second-coordinate).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures

attribute [local implicit_reducible] integralOperationsRoos
  Functor.mapHomologicalComplex CochainComplex.mappingCocone
  integralOperationsTensorComplexFunctor integralOperationsRoosFunctor
  pointIntegralComplexSections pointTensorRoosEndomorphism pointIntegralTensorCompletion
  pointIntegralTensorScalarLeft pointIntegralTensorScalarRight pointIntegralSections
attribute [local irreducible] integralOrdinaryScalar integralOrdinaryTensorSection
  completedIntegralCommRingSheafUnrestricted completedIntegralCoefficientSheafUnrestricted
  coefficientTotalTensor SheafOfModules.monoidalCategory integralOperationsTensorTowerFunctor
  scalarTensorTower scalarTensorChain scalarRoosMap integralOperationsRoosMap

set_option maxHeartbeats 2000000 in
-- Elaborating the ordinary scalar functor and its two Roos product coordinates is large.
/-- Shifted-coordinate normalization for the scalar square.

Source: Stacks 07A4 and 0941.
Proof: both sides are zero. On the left, C₂.second says that the shifted
coordinate of the L-completion vanishes on every element of the section tensor.
On the right, scalarTensorChain = scalarRoosMap ≫ integralOperationsRoosMap is a
map of mapping cocones that is diagonal on the two coordinates, so its shifted
coordinate is the scalar-extended shifted coordinate of its input; the input is
the scalar extension by `a*b` (additive) of the E-completion of `x ⊗ y`, whose
shifted coordinate vanishes by C₁.second. Point sections are additive.
(blueprint: new-lem-sf-point-integral-tensor-scalar-second-coordinate). -/
theorem pointIntegralTensorScalarSecondCoordinate
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (I₁ : PointIntegralTensorData D l hl E) (I₂ : PointIntegralTensorData D l hl L)
    (C₁ : PointIntegralTensorCanonical D l hl E I₁)
    (C₂ : PointIntegralTensorCanonical D l hl L I₂)
    (P Q : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (p q : ℤ)
    (a b : (completedIntegralCommRingSheafUnrestricted l L
      (Spec (.of D.k))).obj.obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k))))))
    (x : (P.obj.X p).val.obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k))))))
    (y : (Q.obj.X q).val.obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k)))))) :
    ((pointIntegralSections l L D.k).map
      ((CochainComplex.mappingCocone.snd
        (pointTensorRoosEndomorphism D l L
          (((integralOrdinaryScalar l E L ι (Spec (.of D.k))).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P.obj)
          (((integralOrdinaryScalar l E L ι (Spec (.of D.k))).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj Q.obj))).v (p + q) (p + q - 1) (by omega)))
      (pointIntegralTensorScalarLeft D l hl E L ι I₁ I₂ C₁ C₂ P Q p q a b x y) =
    ((pointIntegralSections l L D.k).map
      ((CochainComplex.mappingCocone.snd
        (pointTensorRoosEndomorphism D l L
          (((integralOrdinaryScalar l E L ι (Spec (.of D.k))).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P.obj)
          (((integralOrdinaryScalar l E L ι (Spec (.of D.k))).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj Q.obj))).v (p + q) (p + q - 1) (by omega)))
      (pointIntegralTensorScalarRight D l hl E L ι I₁ I₂ C₁ C₂ P Q p q a b x y) := by
  have hleft := C₂.second
    ⟨((integralOrdinaryScalar l E L ι (Spec (.of D.k))).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P.obj, scalarGood l E L ι (Spec (.of D.k)) P⟩
    ⟨((integralOrdinaryScalar l E L ι (Spec (.of D.k))).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj Q.obj, scalarGood l E L ι (Spec (.of D.k)) Q⟩
    (p + q)
    (((HomologicalComplex.ιTensorObj
      ((pointIntegralComplexSections D l L).obj
        (((integralOrdinaryScalar l E L ι (Spec (.of D.k))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P.obj))
      ((pointIntegralComplexSections D l L).obj
        (((integralOrdinaryScalar l E L ι (Spec (.of D.k))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj Q.obj)) p q (p + q) rfl).hom
      (integralOrdinaryTensorSection l E L ι (Spec (.of D.k)) (P.obj.X p)
        (op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k))))) a x ⊗ₜ[
          ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l L)]
        integralOrdinaryTensorSection l E L ι (Spec (.of D.k)) (Q.obj.X q)
          (op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k))))) b y)))
  let z := (HomologicalComplex.ιTensorObj
    ((pointIntegralComplexSections D l E).obj P.obj)
    ((pointIntegralComplexSections D l E).obj Q.obj) p q (p + q) rfl).hom
    (x ⊗ₜ[ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)] y)
  have hzero := C₁.second P Q (p + q) z
  have hlzero : ((pointIntegralSections l L D.k).map
      ((CochainComplex.mappingCocone.snd
        (pointTensorRoosEndomorphism D l L
          (((integralOrdinaryScalar l E L ι (Spec (.of D.k))).mapHomologicalComplex
            (.up ℤ)).obj P.obj)
          (((integralOrdinaryScalar l E L ι (Spec (.of D.k))).mapHomologicalComplex
            (.up ℤ)).obj Q.obj))).v (p + q) (p + q - 1) (by omega)))
      (pointIntegralTensorScalarLeft D l hl E L ι I₁ I₂ C₁ C₂ P Q p q a b x y) = 0 := by
    with_unfolding_all
      simpa only [pointIntegralTensorScalarLeft, sub_eq_add_neg] using! hleft
  rw [hlzero]
  symm
  let F := integralOrdinaryScalar l E L ι (Spec (.of D.k))
  let T := (integralOperationsTensorTowerFunctor l E (Spec (.of D.k))).obj (P.obj, Q.obj)
  let α := (scalarTensorTower l E L ι (Spec (.of D.k))).app (P.obj, Q.obj)
  have hc := (scalarRoosTowerCoordinates α).2 (p + q) (p + q - 1) (by omega)
  have hs := (scalarRoosCoordinates F T).2 (p + q)
  have hcoord : (scalarTensorChain l E L ι (Spec (.of D.k)) P.obj Q.obj).f (p + q) ≫
      (CochainComplex.mappingCocone.snd (pointTensorRoosEndomorphism D l L
        ((F.mapHomologicalComplex (.up ℤ)).obj P.obj)
        ((F.mapHomologicalComplex (.up ℤ)).obj Q.obj))).v
          (p + q) (p + q - 1) (by omega) =
      F.map ((CochainComplex.mappingCocone.snd
        (pointTensorRoosEndomorphism D l E P.obj Q.obj)).v
          (p + q) (p + q - 1) (by omega)) ≫
        (piComparison (F.mapHomologicalComplex (.up ℤ))
          (fun n : ℕ ↦ T.obj (op n))).f (p + q - 1) ≫
        (Limits.Pi.map (fun n : ℕ ↦ α.app (op n))).f (p + q - 1) := by
    unfold scalarTensorChain
    simp only [HomologicalComplex.comp_f]
    with_unfolding_all
      erw [Category.assoc, hc, ← Category.assoc, hs]
      exact Category.assoc _ _ _
  have he := congrArg (fun f ↦ f.val.app
    (op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k)))))) hcoord
  change ((CochainComplex.mappingCocone.snd (pointTensorRoosEndomorphism D l L
      ((F.mapHomologicalComplex (.up ℤ)).obj P.obj)
      ((F.mapHomologicalComplex (.up ℤ)).obj Q.obj))).v
        (p + q) (p + q - 1) (by omega)).val.app _
      (((scalarTensorChain l E L ι (Spec (.of D.k)) P.obj Q.obj).f (p + q)).val.app _
        (integralOrdinaryTensorSection l E L ι (Spec (.of D.k)) _ _ (a * b)
          ((C₁.completion P Q).f (p + q) z))) = 0
  have he' := congrArg (fun f ↦ f
    (integralOrdinaryTensorSection l E L ι (Spec (.of D.k)) _ _ (a * b)
      ((C₁.completion P Q).f (p + q) z))) he
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply] at he'
  with_unfolding_all
    erw [he']
  erw [scalar_map_tensor l E L ι (Spec (.of D.k))]
  have hzero' : ((CochainComplex.mappingCocone.snd
      (pointTensorRoosEndomorphism D l E P.obj Q.obj)).v
        (p + q) (p + q - 1) (by omega)).val.app
      (op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k)))))
      ((C₁.completion P Q).f (p + q) z) = 0 := by
    with_unfolding_all
      simpa only [sub_eq_add_neg] using! hzero
  with_unfolding_all
    erw [hzero']
  simp only [integralOrdinaryTensorSection, TensorProduct.tmul_zero, map_zero]
  with_unfolding_all
    change (((Limits.Pi.map (fun n : ℕ ↦ α.app (op n))).f (p + q - 1)).val.app
      (op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k)))))).hom
      ((((piComparison (F.mapHomologicalComplex (.up ℤ))
        (fun n : ℕ ↦ T.obj (op n))).f (p + q - 1)).val.app _).hom 0) = 0
    simp only [map_zero]

end WeilConjectures
