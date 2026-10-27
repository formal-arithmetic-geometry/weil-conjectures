/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.CoefOpenTensorEvaluationData

/-! # Pointwise evaluation compatibility of native open tensor models

Source: Stacks 0GL1, 07A4; support-open-tensor steps 5--6.
(blueprint: lem-coef-native-open-tensor-gamma-evaluation-component).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
  HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CoefSupportOpenTensor

attribute [-instance] SemilinearSections.hasDerived SemilinearSections.moduleAbelian
  SemilinearSections.abelianSheafify SemilinearSections.locallyBijective
  SemilinearSections.sequenceSmall SemilinearSections.sliceSmall

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The finite evaluation equation for one fixed degree and one fixed pair of derived
objects. It is the pointwise generator-and-descent calculation used to assemble
`GammaEvaluation`; exact evaluation preserves the open unit, restriction comparison,
total summands, and K-flat pullback, while bilinearity and tensor descent extend the
same equality from generators to the displayed derived pair.
Source: Stacks 0GL1 and 07A4, support-open-tensor steps 5--6.
(blueprint: lem-coef-native-open-tensor-gamma-evaluation-component).
-/
theorem nativeOpenTensorGammaEvaluation_component {X Z : Scheme.{u}} (j : X ⟶ Z)
    [IsOpenImmersion j]
    (SX : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (SZ : CoefficientDerivedSystemCalculus.{u, u} l E Z)
    (O : SystemOpenModel l E j SX.toCoefficientDerivedSystemTensors
      SZ.toCoefficientDerivedSystemTensors)
    (On : ∀ n : ℕ, FiniteOpenModel l E j SX.toCoefficientDerivedSystemTensors
      SZ.toCoefficientDerivedSystemTensors n)
    (n : ℕ) (U : coefficientSequenceDerived.{u, u} l E X)
    (L : coefficientSequenceDerived.{u, u} l E Z) :
    (coefficientSequenceDerivedEvaluation.{u, u} l E Z n).map
        ((systemGamma l E j SX.toCoefficientDerivedSystemTensors
          SZ.toCoefficientDerivedSystemTensors O).hom.app (U, L)) ≫
      (ProEtale.VaryingRing.evalJ (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) j n).hom.app
          (SX.systemClosed.tensor.obj (U,
            (ProEtale.VaryingRing.G (compactSupportSystemLevel l E)
              (compactSupportSystemQuotient l E) j).obj L)) ≫
      (ProEtale.StrictTower.moduleJ (compactSupportSystemLevel l E n) j).mapDerivedCategory.map
        ((SX.evaluationTensor n).hom.app (U,
          (ProEtale.VaryingRing.G (compactSupportSystemLevel l E)
            (compactSupportSystemQuotient l E) j).obj L)) ≫
      (ProEtale.StrictTower.moduleJ (compactSupportSystemLevel l E n) j).mapDerivedCategory.map
        ((SX.finiteClosed n).tensor.map (Prod.mkHom (𝟙 _)
          ((ProEtale.VaryingRing.evalG (compactSupportSystemLevel l E)
            (compactSupportSystemQuotient l E) j n).hom.app L))) =
    (SZ.evaluationTensor n).hom.app
        ((ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) j).obj U, L) ≫
      (SZ.finiteClosed n).tensor.map (Prod.mkHom
        ((ProEtale.VaryingRing.evalJ (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) j n).hom.app U) (𝟙 _)) ≫
      (finiteGamma l E j SX.toCoefficientDerivedSystemTensors
        SZ.toCoefficientDerivedSystemTensors n (On n)).hom.app
          ((coefficientSequenceDerivedEvaluation.{u, u} l E X n).obj U,
        (coefficientSequenceDerivedEvaluation.{u, u} l E Z n).obj L) := by
  sorry

end WeilConjectures.CoefSupportOpenTensor
