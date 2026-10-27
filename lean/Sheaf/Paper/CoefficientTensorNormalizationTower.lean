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

/-- Successive finite coefficient tensor normalization, the second component of the coherence.
Source: current blueprint, sec-six-functors/sk-thm-sf-compatibility, fix-prop-coherence.proof.md.
On K-flat representatives both scalar association paths are the same balanced tensor map.
(blueprint: lem-sf-coefficient-tensor-normalization-tower). -/
theorem coefficientTensor_normalization_tower
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p) :
    ∀ (n m : ℕ) (h : m ≤ n),
      let SA := scalarIntegralClosed l E X
      let SB := finiteIntrinsicClosed l E X n
      let SC := finiteIntrinsicClosed l E X m
      let F := coefficientFiniteDerivedExtension l E X n
      let G := coefficientFiniteQuotientDerived l E X h
      let μ := (coefficientDerivedSystemEvaluationCalculus l E X).choose.finiteTensor n
      let ν := (coefficientDerivedSystemEvaluationCalculus l E X).choose.quotientCalculus.tensor h
      let ξ := (coefficientDerivedSystemEvaluationCalculus l E X).choose.finiteTensor m
      let α := Adjunction.leftAdjointCompIso (coefficientFiniteAdjunction l E X n)
        ((coefficientDerivedSystemEvaluationCalculus l E X).choose.quotientCalculus.adjunction h)
        (coefficientFiniteAdjunction l E X m) (normalizedDVRResCompletedComp l E X D hl h)
      ∀ K M : DerivedCategory (scalarReductionSource l E X),
        G.map (μ.hom.app (K, M)) ≫ ν.hom.app (F.obj K, F.obj M) ≫
            SC.tensor.map (Prod.mkHom (α.hom.app K) (α.hom.app M)) =
          α.hom.app (SA.tensor.obj (K, M)) ≫ ξ.hom.app (K, M) := by
  sorry

end WeilConjectures
