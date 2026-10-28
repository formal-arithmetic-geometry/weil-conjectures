/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M7
-/
module

public import Sheaf.SixFunctors.IntegralDualizingSystemTraceData

/-! # Finite exceptional adjunction on the quotient sequence site -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- A trace on the single quotient-system dualizing object, normalized by the
ordinary finite exceptional counits. This assertion does not involve an input K,
a Hom comparison, or invertibility of such a comparison.

Source: prop-coef-integral-dualizing, paragraph 2, reduction-compatible exceptional
counits; Stacks 0941 and 07A6.
(blueprint: lem-coef-system-dualizing-trace-existence).

Proof: use the scalar-restriction descriptions of open extension and proper image
to identify their composite on quotient systems with the native compact-support
functor. The tensor-unit adjunction identifies its finite evaluations with A_n[0].
On a simultaneous K-injective quotient-system resolution of Q, evaluate at n,
use eQ n and the dualizing origin to reach the ordinary finite etale exceptional
object, and apply its exceptional counit. The finite exceptional coefficient
square and hQ show that these quotient-linear counits commute with successor
quotients. Rectify this compatible counit word on the simultaneous resolution
and descend it to the derived quotient-system category. Transport by the support
comparison and the unit comparisons gives trace. The localization comparison for
exact evaluation proves trace_evaluation, with the displayed finite counit word.
This construction uses no test input and no inverse limit. On an empty scheme it
is the unique zero map, and at positive level n+1 the counit is quotient-linear. -/
theorem integralDualizingSystemTraceData_exists
    (S : CoefficientDerivedSystemCalculus l E X)
    (G : CoefPairingSystem l E (finiteDualizingCompactification D X) S)
    (Q : CochainComplex (coefficientSequenceModules l E X) ℤ)
    (eQ : ∀ n : ℕ,
      (coefficientSequenceDerivedEvaluation l E X n).obj (coefTraceInput l E X Q) ≅
        integralDualizingFiniteTerm l E D X n)
    (hQ : ∀ {m n : ℕ} (h : n ≤ m),
      (coefficientSequenceDerivedTransition l E X h).app (coefTraceInput l E X Q) ≫
          (normalizedDVRRes l E X h).map (eQ n).hom =
        (eQ m).hom ≫
          (Adjunction.ofIsRightAdjoint (normalizedDVRRes l E X h)).homEquiv _ _
            (integralDualizingFiniteComparison l E D X hl h)) :
    Nonempty (IntegralDualizingSystemTraceData D l E X S G Q eQ) := by sorry

end WeilConjectures
