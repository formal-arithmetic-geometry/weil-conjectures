/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Derived.DerivedPullbackTensorFiniteConstraints
public import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerRealizationData

/-! # Scalar extension preserves the associator of coherent systems

The derived scalar extension of coherent coefficient systems, with its normalized tensor
comparison `derivedSigma`, is compatible with the associators of the derived tensor products.
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

/-- The normalized whole-system scalar tensorator is compatible with the associators.
Source: Stacks 07A4 and 0FPT (blueprint: lem-pur-derived-pullback-tensor-constraints).
Proof: on flat-term K-flat representatives, the associators descend the strict reassociation
of total-complex summands and the tensorator descends the strict scalar comparison `sigma`.
On a homogeneous local tensor `x ⊗ y ⊗ z` both strict routes give `x ⊗ y ⊗ z` with the
scalar `1`. These generators span the sheafified total tensors, so the strict chain maps agree;
localize, cancel the tensor models and scalar counits, and use naturality to pass from
representatives to arbitrary system objects. -/
theorem systemScalarTensorAssociator
    (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    (M N P : coefficientSequenceDerived l E W) :
    (integralComparisonDerivedSequenceScalar l E L ι W).map
        ((pullbackTensorCalculus l E W).systemClosed.monoidal.associator M N P).hom ≫
      (ScalarExtensionTower.derivedSigma l E L ι W
        (pullbackTensorCalculus l E W) (pullbackTensorCalculus l L W)).hom.app
        (M, (pullbackTensorCalculus l E W).systemClosed.tensor.obj (N, P)) ≫
      (pullbackTensorCalculus l L W).systemClosed.tensor.map
        (Prod.mkHom (𝟙 ((integralComparisonDerivedSequenceScalar l E L ι W).obj M))
          ((ScalarExtensionTower.derivedSigma l E L ι W
            (pullbackTensorCalculus l E W) (pullbackTensorCalculus l L W)).hom.app (N, P))) =
    (ScalarExtensionTower.derivedSigma l E L ι W
        (pullbackTensorCalculus l E W) (pullbackTensorCalculus l L W)).hom.app
        ((pullbackTensorCalculus l E W).systemClosed.tensor.obj (M, N), P) ≫
      (pullbackTensorCalculus l L W).systemClosed.tensor.map
        (Prod.mkHom
          ((ScalarExtensionTower.derivedSigma l E L ι W
            (pullbackTensorCalculus l E W) (pullbackTensorCalculus l L W)).hom.app (M, N))
          (𝟙 ((integralComparisonDerivedSequenceScalar l E L ι W).obj P))) ≫
      ((pullbackTensorCalculus l L W).systemClosed.monoidal.associator
        ((integralComparisonDerivedSequenceScalar l E L ι W).obj M)
        ((integralComparisonDerivedSequenceScalar l E L ι W).obj N)
        ((integralComparisonDerivedSequenceScalar l E L ι W).obj P)).hom := by
  sorry

end WeilConjectures
