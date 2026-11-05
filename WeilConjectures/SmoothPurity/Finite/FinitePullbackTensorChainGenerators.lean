/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorConstruction
import WeilConjectures.SmoothPurity.Coefficient.CoefficientTotalTensorMapGenerators
import WeilConjectures.SmoothPurity.ProEtale.ProEtaleTotalTensorPullbackGenerators

/-! # The explicit intrinsic total pullback tensor isomorphism

Source: Stacks Tags 03EL, 06YY and 07A4.
(blueprint: lem-pur-finite-pullback-tensor-chain-generators).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
universe u
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open MonoidalCategory TensorProduct
namespace WeilConjectures
attribute [local irreducible] Scheme.residueField HasDerivedCategory.standard
  Functor.mapDerivedCategory finitePullbackTensorConstruction
attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
  CategoryTheory.Functor.map₂HomologicalComplex
attribute [local irreducible] SheafOfModules.monoidalCategory
  proEtaleTensorPullbackTotalIso CategoryTheory.Functor.mapBifunctorHomologicalComplex
  HomologicalComplex₂.total
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
attribute [local instance] sfIntrinsicPullback_additive
  pullbackTensorCoefficientFinite
  SheafOfModules.monoidalCategory

/-- The signed-total ordinary comparison conjugated by the prescribed finite realization.
Source: Stacks 03EL and 07A4
(blueprint: lem-pur-finite-pullback-tensor-chain-generators). -/
@[irreducible] def finitePullbackTensorChainIso {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (P Q : CochainComplex (normalizedDVRModules l E Y n) ℤ) :
    ((sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f).mapHomologicalComplex
      (.up ℤ)).obj
        ((coefficientTotalTensor.{u, u + 1, u} (ProEt.topology Y)
          (integralCoefficientCommRingSheaf l E Y n)).obj (P, Q)) ≅
      (coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X)
        (integralCoefficientCommRingSheaf l E X n)).obj
          (((sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f).mapHomologicalComplex
            (.up ℤ)).obj P,
           ((sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f).mapHomologicalComplex
            (.up ℤ)).obj Q) := by
  letI : (sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f).Additive :=
    sfIntrinsicPullback_additive (finiteCoefficientRing l E (n + 1)) f
  let e := NatIso.mapHomologicalComplex (pullbackTensorFiniteRealization l E f n) (.up ℤ)
  exact (e.app ((coefficientTotalTensor.{u, u + 1, u} (ProEt.topology Y)
      (integralCoefficientCommRingSheaf l E Y n)).obj (P, Q))).symm ≪≫
    (proEtaleTensorPullbackTotalIso f
      (integralCoefficientCommRingSheaf l E Y n)
      (integralCoefficientCommRingSheaf l E X n)
      (pullbackTensorCoefficientIso l E f n) P Q).symm ≪≫
    (coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X)
      (integralCoefficientCommRingSheaf l E X n)).mapIso
        (Iso.prod (e.app P) (e.app Q))

end WeilConjectures
