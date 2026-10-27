/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q9
-/
module

public import Sheaf.SixFunctors.CoefTowerEvaluationPairingData
import Sheaf.SixFunctors.CoefPairingFiniteNormalization
import Sheaf.Paper.CoefSupportOpenTensorModel

/-! # Compactification realization of the finite tower pairing

Source: blueprint prop-coef-integral-dualizing, proof paragraph 2,
compact-support and finite projection word
(blueprint: lem-coef-pairing-compactification-models).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable (D : FiniteFieldDatum.{u}) (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- Realize the native quotient-site projection word in the fixed compactification
frame, including its finite comparisons. This concerns compact-support realization
and finite normalization, independently of the Hom representative calculation and
of dinaturality of the resulting morphism.

Source: blueprint prop-coef-integral-dualizing, proof paragraph 2, extracted
steps 4--9; Stacks 07A6, 0B56 and 0941
(blueprint: lem-coef-pairing-compactification-models).

Proof: obtain the coherent derived reduction calculus. Apply projectionEvaluation
to the fixed compactification over D.k, using l different from its characteristic.
Identify its normalized scalar-extension reduction with S.reduction by their
adjunctions to the same total-limit functor and their reduction-unit equations.
Use the coefficient-preserving derived sections comparison to transport the point
square from quotient modules to strict R-module towers. Compose the quotient-point
and scalar-restriction adjunctions: the resulting sections adjunction is the one
in CoefPairingFrame. Pullback composition supplies sourceAdjunction, and canonical
pullback tensor comparisons supply properTensor, sectionsTensor and
restrictionTensor. The open comparison is the actual sheafified chain map of
supportOpenTensorModel; its adjunct is the open unit followed by inverse tensor
restriction, exactly openTensor_adjunct. Exact scalar restriction followed by
separately derived proper image and sections gives compactSections. Perform the
same construction on every finite slice to obtain F. The canonical evaluation
of the pointwise K-flat tensor is evaluationTensor. The full-system scalar-Hom
comparison and the normalized finite Hom comparison give eH. The support and
point-square comparisons give eB; their quotient naturality is the first equation.
Apply the same support comparison to Q and then apply eQ to obtain eQcompact.
Finally pairingFiniteNormalization evaluates the specified scalar-balancing,
sections mate, proper mate, inverse open comparison and closed evaluation word.
Under the above adjunction-preserving comparisons this is definitionally G.beta
and its finite word is coefPairingFiniteBeta. Naturality cancels each adjacent
comparison and its inverse, giving the second equation. This uses neither a
trace nor faithfulness of finite derived evaluation. -/
theorem coefPairingCompactificationModels (hl : l ≠ D.p)
    (Q : CochainComplex (coefficientSequenceModules.{u, u} l E X) ℤ)
    (eQ : ∀ n : ℕ,
      (coefficientSequenceDerivedEvaluation.{u, u} l E X n).obj (coefTraceInput l E X Q) ≅
        integralDualizingFiniteTerm l E D X n) :
    ∃ (S : CoefficientDerivedSystemCalculus l E X)
      (G : CoefPairingSystem l E (finiteDualizingCompactification D X) S)
      (F : ∀ n : ℕ,
        CoefPairingFiniteFrame l E (finiteDualizingCompactification D X) S G n)
      (evaluationTensor : ∀ n : ℕ,
        coefPairingTensor l E ⋙ coefTraceEvaluation l E n ≅
          (coefTraceEvaluation l E n).prod (coefTraceEvaluation l E n) ⋙
            MonoidalCategory.tensor
              (DerivedCategory (ModuleCat.{u + 1} (coefTraceRing l E))))
      (eH : ∀ n : ℕ,
        coefPairingHom l E X S Q ⋙ coefTraceEvaluation l E n ≅
          coefPairingFiniteHom l E X n (integralDualizingFiniteTerm l E D X n))
      (eB : ∀ n : ℕ,
        coefPairingSupport l E D X S ⋙ coefTraceEvaluation l E n ≅
          coefPairingFiniteC l E D X n)
      (eQcompact : ∀ n : ℕ,
        (coefTraceEvaluation l E n).obj (coefTraceDualizingTower l E D X Q) ≅
          (coefPairingFiniteSupport l E (finiteDualizingCompactification D X) n).obj
            (integralDualizingFiniteTerm l E D X n)),
      (∀ (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
        {m n : ℕ} (h : n ≤ m),
        (coefTraceTransition l E h).app ((coefPairingSupport l E D X S).obj K) ≫
          (eB n).hom.app K =
        (eB m).hom.app K ≫
          (coefPairingIntegralSections l E (Spec (.of D.k))).map
            (compactSupportRestrictedTransition l E (finiteDualizingCompactification D X)
              m n h K)) ∧
      (∀ (K : DerivedCategory (scalarReductionSource.{u, u} l E X)),
        finiteTorConstructibleIntegral l E X K → ∀ n : ℕ,
        (coefTraceEvaluation l E n).map
            (G.beta l E (S.reduction.obj K) (coefTraceInput l E X Q)) ≫
          (eQcompact n).hom =
        (evaluationTensor n).hom.app
            ((coefPairingHom l E X S Q).obj (op K), (coefPairingSupport l E D X S).obj K) ≫
          ((eH n).hom.app (op K) ⊗ₘ (eB n).hom.app K) ≫
            coefPairingFiniteBeta l E (finiteDualizingCompactification D X) S G n (F n)
              ((scalarReductionDerivedExtension l E X n).obj K)
              (integralDualizingFiniteTerm l E D X n)) := by sorry

end WeilConjectures
