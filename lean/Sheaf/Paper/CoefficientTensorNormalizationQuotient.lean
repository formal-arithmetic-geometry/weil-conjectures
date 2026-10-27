/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M8
-/
module

public import Sheaf.Paper.FiniteCoefficientHomChange
public import Sheaf.Paper.IntegralOperationsScalarComparisons

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

/-- Quotient tensor associativity normalization, the third component of the coherence.
Source: current blueprint, sec-six-functors/sk-thm-sf-compatibility, fix-prop-coherence.proof.md.
The quotient tensorator is normalized on pure triples and hence respects the derived associator.
(blueprint: lem-sf-coefficient-tensor-normalization-quotient). -/
theorem coefficientTensor_normalization_quotient
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p) :
    ∀ (n m : ℕ) (h : m ≤ n),
      let SA := finiteIntrinsicClosed l E X n
      let SB := finiteIntrinsicClosed l E X m
      let F := coefficientFiniteQuotientDerived l E X h
      let μ := (coefficientDerivedSystemEvaluationCalculus l E X).choose.quotientCalculus.tensor h
      ∀ K M N : normalizedDVRDerived l E X n,
    μ.hom.app (SA.tensor.obj (K, M), N) ≫
        SB.tensor.map (Prod.mkHom (μ.hom.app (K, M)) (𝟙 (F.obj N))) ≫
        (SB.monoidal.associator (F.obj K) (F.obj M) (F.obj N)).hom =
      F.map (SA.monoidal.associator K M N).hom ≫
        μ.hom.app (K, SA.tensor.obj (M, N)) ≫
        SB.tensor.map (Prod.mkHom (𝟙 (F.obj K)) (μ.hom.app (M, N))) := by
  sorry

end WeilConjectures
