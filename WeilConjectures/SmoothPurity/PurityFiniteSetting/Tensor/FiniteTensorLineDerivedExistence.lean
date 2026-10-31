/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorReductionData
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorLineDerivedExistenceWitness

/-! # Derived invertibility of normalized finite signed-line reduction

Source: finite reduction of purity, proof Step 2; Stacks Tags 07A4 and 03EM.
(blueprint: lem-pur-finite-tensor-line-derived-existence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PurityFiniteSetting

/-- A normalized ordinary signed map has a derived comparison at each exponent.
Source: thm-pur-finite-reduction-of-purity, proof Step 2 (invertible twists),
def-coefficient-twists-detailed; Stacks Tags 07A4 and 03EM.
(blueprint: lem-pur-finite-tensor-line-derived-existence).

Proof: each signed line is locally free of rank one, including the internal
duals used at negative exponents. Its degree-zero complex is therefore K-flat.
Compute derived scalar extension on that single complex using the scalar
adjunction's representative map. In ordinary sheaves the adjoint transpose of
c is an isomorphism: on a cover trivializing the integral line it is the
coefficient unit isomorphism. The balancing equation identifies it in degree
one; the tensor recursion does so for positive powers, and the evaluation
equation does so for the dual powers. Isomorphy is local for sheaves. The
fixed-scalar realization/restriction square carries c to finiteTensorFixedLineMap.
Exact restriction commutes with the single functor by the recorded comparison.
The derived adjunction thus identifies the localized ordinary isomorphism with
the prescribed adjoint transpose. No flatness of the coefficient
quotient is used: flatness of the source line justifies the single calculation.
Uniqueness follows by applying injectivity of the actual adjunction homEquiv
to two prescribed transpose equations, then Iso.ext. The argument includes
r = 0, equal levels, and the empty scheme. -/
theorem existsUnique_finiteTensorLineDerivedComparison (P : PurityFiniteSetting.{u})
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level) (T : Scheme.{u})
    [T.Over (Spec (.of P.field.k))]
    (c : P.FiniteTensorLineMaps m hm hmn T)
    (hc : P.FiniteTensorLineMapsNormalized m hm hmn T c) (r : ℤ) :
    ∃! b : (P.finiteTensorReduction m hm hmn T).obj (P.finiteTensorFixedLine T r) ≅
        (P.finiteReductionSetting m hm).finiteTensorFixedLine T r,
      (P.finiteTensorLineComparisonData m hm hmn T).Pointwise c r b := by
  obtain ⟨b, hb⟩ := P.exists_finiteTensorLineDerivedComparison m hm hmn T c hc r
  refine ⟨b, hb, ?_⟩
  intro b' hb'
  exact (P.finiteTensorLineComparisonData m hm hmn T).pointwise_unique c r hb' hb

end WeilConjectures.PurityFiniteSetting
