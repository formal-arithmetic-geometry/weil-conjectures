/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Coefficient.FiniteCoefficientHomChange
public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisons
import all WeilConjectures.SixFunctors.Finite.Hom.FiniteHomSiteEquationDescent
import WeilConjectures.SixFunctors.Finite.Hom.FiniteHomIntrinsicTensorComposition

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedVariables false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

/-- Identity-quotient tensor normalization, the first component of the coefficient tensor coherence.
Source: current blueprint, sec-six-functors/sk-thm-sf-compatibility, fix-prop-coherence.proof.md.
The normalized identity mate is computed on flat representatives by the pure-tensor unit formula.
(blueprint: lem-sf-coefficient-tensor-normalization-unit). -/
theorem coefficientTensor_normalization_unit
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p) :
    ∀ n : ℕ,
      let S := finiteIntrinsicClosed l E X n
      let F := coefficientFiniteQuotientDerived l E X (Nat.le_refl n)
      let μ := (coefficientDerivedSystemEvaluationCalculus l E X).choose.quotientCalculus.tensor
        (Nat.le_refl n)
      let e := Adjunction.leftAdjointIdIso
        ((coefficientDerivedSystemEvaluationCalculus l E X).choose.quotientCalculus.adjunction
          (Nat.le_refl n)) (normalizedDVRResUnit l E X n)
      ∀ K M : normalizedDVRDerived l E X n,
        S.tensor.map (Prod.mkHom (e.inv.app K) (e.inv.app M)) =
          e.inv.app (S.tensor.obj (K, M)) ≫ μ.hom.app (K, M) := by
  have _ := hl
  intro n S F μ e K M
  apply tensor_identity_of_self_composition S F μ e
  intro U V
  simpa [S, F, μ, e, intrinsic_associator_self_unit, coefFiniteHomProTensor,
    coefFiniteHomProUnit, finiteIntrinsicClosed] using
    finiteHomIntrinsic_tensorComposition l E X (Nat.le_refl n) (Nat.le_refl n) U V

end WeilConjectures
