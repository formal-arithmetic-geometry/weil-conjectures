/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientHomChange
public import WeilConjectures.AlgebraicGeometry.IntegralOperationsScalarComparisons

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

/-- Integral-to-finite tensor associativity normalization, the fourth component of the coherence.
Source: current blueprint, sec-six-functors/sk-thm-sf-compatibility, fix-prop-coherence.proof.md.
The finite tensorator is induced by the normalized scalar extension on flat representatives.
(blueprint: lem-sf-coefficient-tensor-normalization-finite). -/
theorem coefficientTensor_normalization_finite
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p) :
    ∀ n : ℕ,
      let SA := scalarIntegralClosed l E X
      let SB := finiteIntrinsicClosed l E X n
      let F := coefficientFiniteDerivedExtension l E X n
      let μ := (coefficientDerivedSystemEvaluationCalculus l E X).choose.finiteTensor n
      ∀ K M N : DerivedCategory (scalarReductionSource l E X),
    μ.hom.app (SA.tensor.obj (K, M), N) ≫
        SB.tensor.map (Prod.mkHom (μ.hom.app (K, M)) (𝟙 (F.obj N))) ≫
        (SB.monoidal.associator (F.obj K) (F.obj M) (F.obj N)).hom =
      F.map (SA.monoidal.associator K M N).hom ≫
        μ.hom.app (K, SA.tensor.obj (M, N)) ≫
        SB.tensor.map (Prod.mkHom (𝟙 (F.obj K)) (μ.hom.app (M, N))) := by
  sorry

end WeilConjectures
