/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorTraceScalar.VectorTraceScalarData
import WeilConjectures.CategoryTheory.Exact.ExactDegreeZeroSupplement
import all WeilConjectures.AlgebraicGeometry.P1.P1CounitScalar
import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientUnitCoherence
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryChartSingleUnitor
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryChartUnitNormalization

/-! # Scalar compatibility of tensoring with the ordinary single unit

Source: blueprint smooth-purity reduction, Charts.
(blueprint: lem-pur-ordinary-chart-single-unit-scalar).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
attribute [local instance 10000] SheafExactDegreeZero.scalarWeakSheafify
attribute [local implicit_reducible] constantSheaf
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
attribute [local implicit_reducible] sheafMonoidalCategory sheafBraidedCategory
attribute [local instance 21000] sheafBraidedCategory
attribute [local instance 20000] SymmetricCategory.toBraidedCategory
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  ProEtale.pbcFixedScalarExtension derivedTensor upperStar lowerStar
  projectiveLineTraceDatum projectiveLineTraceTransport
  WeilConjectures.PurityFiniteSetting.purityScalarSingleMap
  WeilConjectures.PurityFiniteSetting.purityScalarUnitMap
  ExceptionalCoefficients.tensorIso ExceptionalCoefficients.unitIso
  singleFunctorObjUnitIso derivedTensorRightUnitor
  HasDerivedCategory.ofIsGrothendieckAbelian HasDerivedCategory.ofHasKInjectiveResolutions
  _root_.DerivedCategory.singleFunctors

/-- Scalar compatibility of tensoring with the ordinary single unit.
Source: blueprint smooth-purity reduction, Charts.
(blueprint: lem-pur-ordinary-chart-single-unit-scalar).

Proof: Express both single-unit unitors through the genuine monoidal right unitors, using the two
normalization equations.
Apply the coefficient tensorator right-unit coherence square. The generic transported-right-unit
identity pastes that square with the chosen unit identifications and the transported coefficient
unit equation. -/
theorem ordinaryChartSingleUnitScalarSquare
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    (T : Scheme.{u}) (K : DerivedCategoryModule A T) :
    (ExceptionalCoefficients.tensorIso φ T).hom.app (K, ordinaryFiniteUnit A T) ≫
      ((ordinaryFiniteTensor B T).obj ((scalarExtension φ T).obj K)).map
        (VectorTraceScalar.unit φ T) ≫
      (derivedTensorSingleUnitIso ((scalarExtension φ T).obj K)).hom =
      (scalarExtension φ T).map (derivedTensorSingleUnitIso K).hom := by
  exact transported_right_unit_named (scalarExtension φ T)
    (ordinaryFiniteTensor A T) (ordinaryFiniteTensor B T)
    (ExceptionalCoefficients.tensorIso φ T).hom K
    (ordinaryFiniteUnit A T) (𝟙_ _) (ordinaryFiniteUnit B T) (𝟙_ _)
    (ordinaryFiniteSingleUnitIso A T) (ordinaryFiniteSingleUnitIso B T)
    (ExceptionalCoefficients.unitIso φ T).hom
    (derivedTensorRightUnitor (ModuleCat.{u + 1} A) T K).hom
    (derivedTensorRightUnitor (ModuleCat.{u + 1} B) T
      ((scalarExtension φ T).obj K)).hom
    (VectorTraceScalar.unit φ T) (derivedTensorSingleUnitIso K).hom
    (derivedTensorSingleUnitIso ((scalarExtension φ T).obj K)).hom
    (ordinaryChartUnitMap_eq φ T)
    (ordinaryChartSingleUnitor_eq T K)
    (ordinaryChartSingleUnitor_eq T ((scalarExtension φ T).obj K))
    (ExceptionalCoefficients.tensorIso_right_unit φ T K)

end AlgebraicGeometry.Etale
