/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralFiniteExtension.IntegralHomTensorAdjointRepresentatives
public import WeilConjectures.SmoothPurity.PurCompactSupport.IntegralCompactSupportScalarTensor
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement

/-! # Pure generators for inverse scalar balancing

Source: Stacks Tags 03EL, 06YY, 07A4 and 0FPQ.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralFiniteExtension

attribute [local instance 2000]
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

attribute [local instance 100000] CategoryTheory.HasSheafify.isRightAdjoint
  CategoryTheory.Limits.HasColimitsOfShape.has_colimit
  SheafOfModules.instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf
  SheafOfModules.instHasColimitsOfSizeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf

attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  CategoryTheory.Functor.mapBifunctorHomologicalComplex HomologicalComplex₂.total
  tensorComplexSwap PurCompactSupport.scalarTensorTotal PurCompactSupport.scalarOrdinaryTensor
  CategoryTheory.presheafToSheaf CategoryTheory.Functor.leftAdjoint
  limit coefficientTensorGenerator

attribute [-instance] IntegralHom.ordinaryTensorZero IntegralHom.ordinaryTensorObjZero in
private theorem scalar_total_ι {X : Scheme.{u}}
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (P Q : CochainComplex (pbcModules X R) ℤ) (p q n : ℤ) (h : p + q = n) :
    (pbcExtend φ).map
        (CochainComplex.ιMapBifunctor P Q (proEtaleOrdinaryTensor X R) p q n h) ≫
      (@inv _ _ _ _ (PurCompactSupport.scalarTensorTotal φ P Q)
        (PurCompactSupport.scalarTensorTotal_isIso φ P Q)).f n =
    (PurCompactSupport.scalarOrdinaryTensor φ (P.X p) (Q.X q)).hom ≫
      CochainComplex.ιMapBifunctor
        (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj P)
        (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj Q)
        (proEtaleOrdinaryTensor X S) p q n h := by
  let e := @asIso _ _ _ _ (PurCompactSupport.scalarTensorTotal φ P Q)
    (PurCompactSupport.scalarTensorTotal_isIso φ P Q)
  change _ ≫ e.inv.f n = _
  apply (cancel_mono (e.hom.f n)).1
  simp only [Category.assoc, ← HomologicalComplex.comp_f, Iso.inv_hom_id,
    HomologicalComplex.id_f, Category.comp_id]
  change _ = _ ≫ _ ≫ (PurCompactSupport.scalarTensorTotal φ P Q).f n
  simp only [PurCompactSupport.scalarTensorTotal, tensorPullbackTotal,
    tensorPullbackTotalComponent, HomologicalComplex.ι_mapBifunctorDesc,
    Iso.hom_inv_id_assoc]

attribute [-instance] IntegralHom.ordinaryTensorZero IntegralHom.ordinaryTensorObjZero in
/-- The inverse total scalar tensor map sends a pure generator with coefficient one
 to the tensor of the two scalar-unit sections.
Source: Stacks 03EL and 07A4
(blueprint: new-sf-integral-scalar-tensor-total-generators). -/
theorem scalarTensorTotal_inverse_generator {X : Scheme.{u}}
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (P Q : CochainComplex (pbcModules X R) ℤ) (p q n : ℤ) (h : p + q = n)
    (U : X.ProEtᵒᵖ) (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) :
    ((@inv _ _ _ _ (PurCompactSupport.scalarTensorTotal φ P Q)
      (PurCompactSupport.scalarTensorTotal_isIso φ P Q)).f n).val.app U
      (pbcTensorSection φ _ U 1
        (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X) R
          P Q p q n h U x y)) =
    coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X) S
      (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj P)
      (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj Q) p q n h U
      (pbcTensorSection φ (P.X p) U 1 x) (pbcTensorSection φ (Q.X q) U 1 y) := by
  have hn := reductionTensor_map X φ
    (CochainComplex.ιMapBifunctor P Q (proEtaleOrdinaryTensor X R) p q n h)
    U 1 (proEtaleTensorPair X R (P.X p) (Q.X q) U x y)
  have hi := congrArg (fun f ↦ f.val.app U
    (pbcTensorSection φ _ U 1 (proEtaleTensorPair X R (P.X p) (Q.X q) U x y)))
    (scalar_total_ι φ P Q p q n h)
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply] at hi
  simp only [pbcTensorSection, reductionTensorSection] at hn hi ⊢
  rw [hn] at hi
  have hμ := (PurCompactSupport.scalarOrdinaryTensor_existsUnique φ).exists.choose_spec
    (P.X p) (Q.X q) U 1 x y
  simp only [PurCompactSupport.scalarOrdinaryTensor] at hi
  simp only [pbcTensorSection] at hμ
  rw [hμ] at hi
  convert hi using 0
  with_unfolding_all rfl

set_option maxHeartbeats 800000 in
-- Comparing the two total tensor implementations requires explicit definitional conversion.
/-- Following inverse scalar balancing by Koszul exchange gives the signed
reversed total generator of the two scalar-unit sections.
Source: Stacks 03EL, 07A4 and 0FPQ
(blueprint: new-sf-integral-scalar-tensor-total-generators). -/
theorem scalarTensorTotal_exchange_generator {X : Scheme.{u}}
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (P Q : CochainComplex (pbcModules X R) ℤ) (p q : ℤ)
    (U : X.ProEtᵒᵖ) (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) :
    (((@inv _ _ _ _ (PurCompactSupport.scalarTensorTotal φ P Q)
        (PurCompactSupport.scalarTensorTotal_isIso φ P Q)) ≫
      (tensorComplexSwap X S
        (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj P)
        (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj Q)).hom).f (p + q)).val.app U
      (pbcTensorSection φ _ U 1
        (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X) R
          P Q p q (p + q) rfl U x y)) =
    ((p * q).negOnePow : ℤ) •
      coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X) S
        (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj Q)
        (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj P)
        q p (p + q) (add_comm q p) U
        (pbcTensorSection φ (Q.X q) U 1 y) (pbcTensorSection φ (P.X p) U 1 x) := by
  simp only [HomologicalComplex.comp_f, SheafOfModules.comp_val,
    PresheafOfModules.comp_app, ModuleCat.comp_apply]
  rw [scalarTensorTotal_inverse_generator]
  have hswap := tensorComplexSwap_pure X S
    (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj P)
    (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj Q)
    p q (p + q) rfl (add_comm q p) U
    (pbcTensorSection φ (P.X p) U 1 x) (pbcTensorSection φ (Q.X q) U 1 y)
  simp only [Units.smul_def] at hswap
  convert hswap using 0
  with_unfolding_all rfl

end WeilConjectures.IntegralFiniteExtension
