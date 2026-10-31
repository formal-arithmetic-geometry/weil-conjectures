/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralDualizingSystemTraceData
public import WeilConjectures.SixFunctors.CoefPairingExceptionalTests

/-! # Etale origin of finite scalar tensor tests

Source: prop-coef-integral-dualizing.proof.md, second proof paragraph.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- Finite evaluation of a scalar tensor test has an unbounded etale origin.
Source: prop-coef-integral-dualizing.proof.md, paragraph 2, finite scalar tensor tests
(blueprint: lem-coef-finite-tensor-test-etale-origin).

Proof: compose the source sections adjunction of G with the scalar tower evaluation
adjunction. The right adjoint is sections followed by finite scalar evaluation.
The coefficient sections evaluation comparison identifies it with finite evaluation
followed by actual finite sections. Construct the derived finite-prefix extension
L_n left adjoint to finite evaluation; its unit is invertible since its nth value
is identity coefficient extension. The composite of L_n with the finite constant
scalar functor is therefore left adjoint to the same right adjoint as the source
test. Uniqueness of left adjoints, then evaluation and the unit of L_n, identify
the evaluated source test with the derived constant sheaf of the finite scalar
extension of T. The reduction
comparison of S and integral constructibility give a bounded constructible etale
origin J_K of the finite reduction of K. Exact monoidal site comparison identifies
the tensor of the etale constant complex and J_K with the displayed finite tensor:
first use the scalar tensor realization on K-flat representatives, then the
specified evaluationTensor and reductionEvaluation isomorphisms of S. Neither T
nor this tensor is asserted bounded; zero T and empty X use the zero origin. -/
theorem integralDualizingFiniteTest_etaleOrigin
    (S : CoefficientDerivedSystemCalculus l E X)
    (G : CoefPairingSystem l E (finiteDualizingCompactification D X) S)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (hK : finiteTorConstructibleIntegral l E X K) (n : ℕ)
    (T : DerivedCategory (ModuleCat.{u + 1} (coefTraceRing l E))) :
    ∃ J : Etale.DerivedCategoryModule (finiteDualizingCoeff l E n) X,
      Nonempty ((finiteDualizingRealization l E X n).obj J ≅
        (coefficientSequenceDerivedEvaluation l E X n).obj
          (S.systemClosed.tensor.obj
            ((G.frame.testPull S.systemClosed G.baseTensors.systemClosed).obj
              ((coefPairingEvaluationLeft l E n).obj T), S.reduction.obj K))) := by
  sorry

end WeilConjectures
