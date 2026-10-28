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

include hl in
/-- Every finite evaluation of the explicitly transposed, normalized system trace
is invertible on an integral constructible input. Naturality in the input and
assembly of tower maps are not part of this assertion.

Source: prop-coef-integral-dualizing, paragraph 2, the finite mapping-complex
comparison; Stacks 08J9, 07A6 and 0941.
(blueprint: lem-coef-system-exceptional-transpose-finite-isomorphism).

Proof: fix K and n. Integral residue Tor invariance places the nth reduction of K
in the finite-Tor constructible domain. Evaluate the two adjunction transposes
that define integralDualizingSystemAdjunctionMap. The exact tensor/sections
comparisons identify their projection and evaluation factors with the finite
ones. The trace_evaluation equation replaces the final factor with the ordinary
exceptional counit under the fixed dualizing origin eQ n. Finite duality site
comparison identifies this word with the etale internal exceptional adjunction
for that finite-Tor input and the coefficient unit, hence with an isomorphism.
Transport through the scalar and site comparison isomorphisms and forget to the
completed scalar module. This proves the displayed IsIso statement. Only the Tor
interval of this fixed input is used; for zero input both sides are zero. -/
theorem integralDualizingSystemAdjunctionMap_evaluation_isIso
    (S : CoefficientDerivedSystemCalculus l E X)
    (G : CoefPairingSystem l E (finiteDualizingCompactification D X) S)
    (Q : CochainComplex (coefficientSequenceModules l E X) ℤ)
    (eQ : ∀ n : ℕ,
      (coefficientSequenceDerivedEvaluation l E X n).obj (coefTraceInput l E X Q) ≅
        integralDualizingFiniteTerm l E D X n)
    (t : IntegralDualizingSystemTraceData D l E X S G Q eQ)
    (K : (sfIntegralConstructibleCategory l E X)ᵒᵖ) (n : ℕ) :
    IsIso ((coefPairingDerivedEvaluation l E n).map
      ((integralDualizingSystemAdjunctionMap D l E X S G Q t.trace).app K)) := by sorry

end WeilConjectures
