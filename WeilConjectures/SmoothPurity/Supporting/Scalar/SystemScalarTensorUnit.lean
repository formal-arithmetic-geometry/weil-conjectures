/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Derived.DerivedPullbackTensorFiniteConstraints
public import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerRealizationData

/-! # Scalar extension preserves the unit of coherent systems

The derived scalar extension of coherent coefficient systems sends the tensor unit to the
tensor unit, compatibly with the normalized tensor comparison `derivedSigma` and both unitors.
Source: Stacks Project, Tags 07A4 and 0FPT.
(blueprint: lem-pur-derived-pullback-tensor-constraints).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- The derived scalar extension of coherent systems preserves the tensor unit, compatibly with
the normalized tensorator and both unitors.
Source: Stacks 07A4 and 0FPT (blueprint: lem-pur-derived-pullback-tensor-constraints).
Proof: the unit is the coefficient ring in degree zero, a flat-term K-flat complex, and its
strict scalar extension is the coefficient ring of the larger field. On representatives the
right unitor descends scalar multiplication `x ⊗ a ↦ a • x`, and the strict scalar comparison
sends `x ⊗ a` to `x ⊗ a`; both routes give `a • x`. The left unitor is the right unitor composed
with the symmetry, which is compatible with the tensorator by `systemScalarTensorBraiding`. -/
theorem systemScalarTensorUnit
    (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)] :
    ∃ e : (integralComparisonDerivedSequenceScalar l E L ι W).obj
        (pullbackTensorCalculus l E W).systemClosed.monoidal.tensorUnit ≅
        (pullbackTensorCalculus l L W).systemClosed.monoidal.tensorUnit,
      ∀ A : coefficientSequenceDerived l E W,
        (ScalarExtensionTower.derivedSigma l E L ι W
            (pullbackTensorCalculus l E W) (pullbackTensorCalculus l L W)).hom.app
            ((pullbackTensorCalculus l E W).systemClosed.monoidal.tensorUnit, A) ≫
          (pullbackTensorCalculus l L W).systemClosed.tensor.map
            (Prod.mkHom e.hom (𝟙 ((integralComparisonDerivedSequenceScalar l E L ι W).obj A))) ≫
          ((pullbackTensorCalculus l L W).systemClosed.monoidal.leftUnitor
            ((integralComparisonDerivedSequenceScalar l E L ι W).obj A)).hom =
        (integralComparisonDerivedSequenceScalar l E L ι W).map
          ((pullbackTensorCalculus l E W).systemClosed.monoidal.leftUnitor A).hom ∧
        (ScalarExtensionTower.derivedSigma l E L ι W
            (pullbackTensorCalculus l E W) (pullbackTensorCalculus l L W)).hom.app
            (A, (pullbackTensorCalculus l E W).systemClosed.monoidal.tensorUnit) ≫
          (pullbackTensorCalculus l L W).systemClosed.tensor.map
            (Prod.mkHom (𝟙 ((integralComparisonDerivedSequenceScalar l E L ι W).obj A)) e.hom) ≫
          ((pullbackTensorCalculus l L W).systemClosed.monoidal.rightUnitor
            ((integralComparisonDerivedSequenceScalar l E L ι W).obj A)).hom =
        (integralComparisonDerivedSequenceScalar l E L ι W).map
          ((pullbackTensorCalculus l E W).systemClosed.monoidal.rightUnitor A).hom := by
  sorry

end WeilConjectures
