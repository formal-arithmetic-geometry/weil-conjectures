/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralFiniteExtension.IntegralHomTensorAdjointRepresentatives
public import WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import WeilConjectures.SixFunctors.IntegralFiniteExtension.IntegralScalarTensorTotalGenerators
import WeilConjectures.SixFunctors.IntegralFiniteExtension.IntegralScalarTensorOrdinarySourceGenerators
import all WeilConjectures.CategoryTheory.Scalar.ScalarHomTensorCoherence

/-! # Ordinary scalar tensor transport and signed interchange

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
  integralCompletedScalarMap completedCoefficientMap
  CategoryTheory.presheafToSheaf CategoryTheory.Functor.leftAdjoint
  limit coefficientTensorGenerator

set_option maxHeartbeats 800000 in
-- Comparing the two ordinary scalar models requires unfolding their shared witness.
/-- Pure-tensor normalization of an ordinary scalar model comparison is compatible
with total tensor and Koszul exchange, before passage to the derived category.

Source: Stacks Tags 03EL, 06YY, 07A4 and 0FPQ; the ordinary scalar calculation
in paragraph 5 of lem-coef-integral-finite-extension.proof.md.

Proof: use the scalar extension adjunction in each total degree, then test the
resulting maps on pure sections in each tensor summand. The source exchange
contributes (-1)^(pq). The ordinary tensor comparison and t send the two factors
to their fixed scalar-unit sections. On the other path the inverse ordinary
balancing comparison has this same pure-section formula, and target exchange
contributes the identical sign. Equality on pure tensors and total summands
proves equality of chain maps. No K-flatness or derived counit is involved.
(blueprint: new-sf-integral-scalar-tensor-ordinary-transport). -/
theorem scalarTensor_ordinary_transport
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (X : Scheme.{u})
    (t : integralOrdinaryScalar l E L ι X ≅
      completedOrdinaryScalarExtension.{u, u} l E L ι X)
    (ht : ∀ (N : integralTowerModules l E X) (U : X.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l L X).obj.obj U)
      (x : N.val.obj U),
      (t.hom.app N).val.app U (integralOrdinaryTensorSection l E L ι X N U s x) =
        completedScalarTensorSection.{u, u} l E L ι X N U s x)
    (P Q : CochainComplex (integralTowerModules l E X) ℤ) :
    ((integralOrdinaryScalar l E L ι X).mapHomologicalComplex (.up ℤ)).map
        (tensorComplexSwap X (completedIntegralCommRingSheafUnrestricted l E X) P Q).hom ≫
      (scalarOrdinaryTensorChain l E L ι X).hom.app (Q, P) ≫
      (coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X)
        (completedIntegralCommRingSheafUnrestricted l L X)).map
          (Prod.mkHom ((NatIso.mapHomologicalComplex t (.up ℤ)).hom.app Q)
            ((NatIso.mapHomologicalComplex t (.up ℤ)).hom.app P)) =
    (NatIso.mapHomologicalComplex t (.up ℤ)).hom.app
        (((IntegralHom.totalTensor.{u, u} X
          (completedIntegralCommRingSheafUnrestricted l E X)).obj P).obj Q) ≫
      @inv _ _ _ _ (PurCompactSupport.scalarTensorTotal
          (completedCoefficientMap l E L ι X) P Q)
        (PurCompactSupport.scalarTensorTotal_isIso (completedCoefficientMap l E L ι X) P Q) ≫
      (tensorComplexSwap X (completedIntegralCommRingSheafUnrestricted l L X)
        (((pbcExtend (completedCoefficientMap l E L ι X)).mapHomologicalComplex (.up ℤ)).obj P)
        (((pbcExtend (completedCoefficientMap l E L ι X)).mapHomologicalComplex
          (.up ℤ)).obj Q)).hom := by
  let J := ProEt.topology X
  let R := completedIntegralCommRingSheafUnrestricted l E X
  let S := completedIntegralCommRingSheafUnrestricted l L X
  let φ := completedCoefficientMap l E L ι X
  let τ := NatIso.mapHomologicalComplex t (.up ℤ)
  let FP := ((integralOrdinaryScalar l E L ι X).mapHomologicalComplex (.up ℤ)).obj P
  let FQ := ((integralOrdinaryScalar l E L ι X).mapHomologicalComplex (.up ℤ)).obj Q
  let GP := ((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj P
  let GQ := ((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj Q
  apply HomologicalComplex.hom_ext
  intro n
  apply scalarOrdinary_total_hom_ext l E L ι X P Q n
  intro p q hpq U x y
  subst n
  change (((coefficientTotalTensor.{u, u + 1, u} J S).map
      (Prod.mkHom (τ.hom.app Q) (τ.hom.app P))).f (p + q)).val.app U
      (((scalarOrdinaryTensorChain l E L ι X).hom.app (Q, P)).f (p + q) |>.val.app U
        ((integralOrdinaryScalar l E L ι X).map
            ((tensorComplexSwap X R P Q).hom.f (p + q)) |>.val.app U
          (integralOrdinaryTensorSection l E L ι X _ U 1
            (coefficientTensorGenerator.{u, u + 1, u} J R P Q p q (p + q) rfl U x y)))) =
    ((tensorComplexSwap X S GP GQ).hom.f (p + q)).val.app U
      ((@inv _ _ _ _ (PurCompactSupport.scalarTensorTotal φ P Q)
        (PurCompactSupport.scalarTensorTotal_isIso φ P Q)).f (p + q) |>.val.app U
          (((τ.hom.app _).f (p + q)).val.app U
            (integralOrdinaryTensorSection l E L ι X _ U 1
              (coefficientTensorGenerator.{u, u + 1, u} J R P Q p q (p + q) rfl U x y))))
  have hs := scalarTensor_ordinary_source_generator l E L ι X P Q p q U x y
  simp only [HomologicalComplex.comp_f, SheafOfModules.comp_val,
    PresheafOfModules.comp_app, ModuleCat.comp_apply] at hs
  erw [hs]
  simp only [map_zsmul]
  erw [CategoryTheory.ScalarHomTensor.tensor_generator_map.{u + 1, u, u}]
  have ht' (A : CochainComplex (integralTowerModules l E X) ℤ) (i : ℤ)
      (z : (A.X i).val.obj U) :
      ((τ.hom.app A).f i).val.app U
        (integralOrdinaryTensorSection l E L ι X (A.X i) U 1 z) =
      pbcTensorSection φ (A.X i) U 1 z := ht (A.X i) U 1 z
  rw [ht', ht']
  erw [ht']
  have hg := scalarTensorTotal_exchange_generator φ P Q p q U x y
  simp only [HomologicalComplex.comp_f, SheafOfModules.comp_val,
    PresheafOfModules.comp_app, ModuleCat.comp_apply] at hg
  exact hg.symm

end WeilConjectures.IntegralFiniteExtension
