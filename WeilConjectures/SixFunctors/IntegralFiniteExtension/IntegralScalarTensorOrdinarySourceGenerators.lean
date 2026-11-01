/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralFiniteExtension.IntegralHomTensorAdjointRepresentatives
public import WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import all WeilConjectures.SmoothPurity.Scalar.ScalarExtensionComposition
import all WeilConjectures.CategoryTheory.Scalar.ScalarHomTensorCoherence
import all WeilConjectures.SmoothPurity.PurCompactSupport.IntegralCompactSupportScalarTensor

/-! # Ordinary scalar tensor generators and extensionality

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
  completedIntegralCommRingSheafUnrestricted completedIntegralCoefficientSheafUnrestricted
  integralOrdinaryScalar integralOrdinaryTensorSection scalarOrdinaryTensorChain
  tensorComplexSwap PurCompactSupport.scalarTensorTotal PurCompactSupport.scalarOrdinaryTensor
  integralCompletedScalarMap completedCoefficientMap scalarAdjunction
  CategoryTheory.presheafToSheaf CategoryTheory.Functor.leftAdjoint
  limit coefficientTensorGenerator

/-- On a pure total generator, source Koszul exchange followed by the ordinary
scalar tensor comparison contributes exactly the Koszul sign.
Source: Stacks 03EL, 07A4 and 0FPQ
(blueprint: new-sf-integral-scalar-tensor-ordinary-source-generators). -/
theorem scalarTensor_ordinary_source_generator
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (X : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E X) ℤ) (p q : ℤ)
    (U : X.ProEtᵒᵖ) (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) :
    ((((integralOrdinaryScalar l E L ι X).mapHomologicalComplex (.up ℤ)).map
        (tensorComplexSwap X (completedIntegralCommRingSheafUnrestricted l E X) P Q).hom ≫
      (scalarOrdinaryTensorChain l E L ι X).hom.app (Q, P)).f (p + q)).val.app U
        (integralOrdinaryTensorSection l E L ι X _ U 1
          (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X)
            (completedIntegralCommRingSheafUnrestricted l E X)
            P Q p q (p + q) rfl U x y)) =
      ((p * q).negOnePow : ℤ) •
        coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X)
          (completedIntegralCommRingSheafUnrestricted l L X)
          (((integralOrdinaryScalar l E L ι X).mapHomologicalComplex (.up ℤ)).obj Q)
          (((integralOrdinaryScalar l E L ι X).mapHomologicalComplex (.up ℤ)).obj P)
          q p (p + q) (add_comm q p) U
          (integralOrdinaryTensorSection l E L ι X (Q.X q) U 1 y)
          (integralOrdinaryTensorSection l E L ι X (P.X p) U 1 x) := by
  let J := ProEt.topology X
  let R := completedIntegralCommRingSheafUnrestricted l E X
  let S := completedIntegralCommRingSheafUnrestricted l L X
  let FP := ((integralOrdinaryScalar l E L ι X).mapHomologicalComplex (.up ℤ)).obj P
  let FQ := ((integralOrdinaryScalar l E L ι X).mapHomologicalComplex (.up ℤ)).obj Q
  simp only [HomologicalComplex.comp_f, SheafOfModules.comp_val,
    PresheafOfModules.comp_app, ModuleCat.comp_apply]
  erw [scalar_map_tensor]
  have hs := tensorComplexSwap_pure X R P Q p q (p + q) rfl
    (add_comm q p) U x y
  rw [hs]
  have hκ := (scalarOrdinaryTensorChain_existsUnique l E L ι X).exists.choose_spec
    Q P q p U y x
  have hκn (n : ℤ) (hn : q + p = n) :
      (((scalarOrdinaryTensorChain l E L ι X).hom.app (Q, P)).f n).val.app U
      (integralOrdinaryTensorSection l E L ι X _ U 1
        (coefficientTensorGenerator.{u, u + 1, u} J R Q P q p n
          hn U y x)) =
    coefficientTensorGenerator.{u, u + 1, u} J S FQ FP q p n
      hn U
      (integralOrdinaryTensorSection l E L ι X (Q.X q) U 1 y)
      (integralOrdinaryTensorSection l E L ι X (P.X p) U 1 x) := by
    subst n
    simpa only [scalarOrdinaryTensorChain] using hκ
  have hκ' := hκn (p + q) (add_comm q p)
  have hsign (N : integralTowerModules l E X) (z : N.val.obj U) (k : ℤ) :
      integralOrdinaryTensorSection l E L ι X N U 1 (k • z) =
        k • integralOrdinaryTensorSection l E L ι X N U 1 z := by
    rw [← scalarAdjunction_unit, ← scalarAdjunction_unit]
    exact map_zsmul (((scalarAdjunction l E L ι X).unit.app N).val.app U).hom k z
  simp only [Units.smul_def]
  rw [hsign]
  simp only [map_zsmul]
  erw [hκ']

/-- Maps from ordinary scalar extension of a total tensor are detected on the
scalar-unit images of its pure total generators.
Source: Stacks 03EL and 07A4, ordinary scalar adjunction and tensor sheafification
(blueprint: new-sf-integral-scalar-tensor-ordinary-source-generators). -/
theorem scalarOrdinary_total_hom_ext
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (X : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E X) ℤ) (n : ℤ)
    (V : integralTowerModules l L X)
    {f g : (integralOrdinaryScalar l E L ι X).obj
      (((coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X)
        (completedIntegralCommRingSheafUnrestricted l E X)).obj (P, Q)).X n) ⟶ V}
    (h : ∀ (p q : ℤ) (hpq : p + q = n) (U : X.ProEtᵒᵖ)
        (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
      f.val.app U (integralOrdinaryTensorSection l E L ι X _ U 1
        (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X)
          (completedIntegralCommRingSheafUnrestricted l E X) P Q p q n hpq U x y)) =
      g.val.app U (integralOrdinaryTensorSection l E L ι X _ U 1
        (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X)
          (completedIntegralCommRingSheafUnrestricted l E X) P Q p q n hpq U x y))) :
    f = g := by
  apply ((scalarAdjunction l E L ι X).homEquiv _ _).injective
  erw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply CategoryTheory.ScalarHomTensor.total_pure_hom_ext.{u + 1, u, u} P Q n
  intro p q hpq U x y
  change f.val.app U (((scalarAdjunction l E L ι X).unit.app _).val.app U
      (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X)
        (completedIntegralCommRingSheafUnrestricted l E X) P Q p q n hpq U x y)) =
    g.val.app U (((scalarAdjunction l E L ι X).unit.app _).val.app U
      (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X)
        (completedIntegralCommRingSheafUnrestricted l E X) P Q p q n hpq U x y))
  erw [scalarAdjunction_unit]
  exact h p q hpq U x y

end WeilConjectures.IntegralFiniteExtension
