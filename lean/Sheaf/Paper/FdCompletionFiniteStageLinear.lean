/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M4
-/
module

public import Sheaf.Paper.FdCompletionInverseScalarCoherence
public import Sheaf.Paper.IntrinsicQbarCategory

/-! # Finite-field linearity of the normalized scalar comparison

Source: blueprint coefficient comparison, trace-definition final sentence, and
smooth-purity transport Steps 2 and 4.
-/

@[expose] public section
set_option autoImplicit false
universe d u w
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- Normalized tensor formulas give linearity over the actual intermediate field.
Source: trace-definition coefficient comparison Steps 2 and 6; smooth-purity
transport Steps 2 and 4
(blueprint: lem-pur-completion-finite-stage-linear).

Proof: fix E. The rational equivalence sends each pure tensor a tensor f to the
pure tensor with scalar transported by pbcRationalCoefficientEquiv inverse composed
with sfRationalCoefficientEquiv, and integral arrow sent by the integral functor.
Its additivity extends this formula to all sums of pure tensors. Multiplying a
pure tensor by a localization scalar multiplies its first factor, so the formula
also gives semilinearity on every localized arrow by tensor induction. The PBC
field equivalence qbarStageFieldEquiv equals pbcRationalCoefficientEquiv followed
by Shrink.algEquiv: both fix all integral numerators, which determine a map from
the uniformizer localization. The framework equivalence is sfRationalCoefficientEquiv
followed by the same Shrink.algEquiv. Thus the two scalar transport formulas
identify the semilinearity equation with E-linearity. Finally transfer the result
through c.finite_functor. This includes the zero object and zero morphisms and
requires no faithfulness of scalar transitions. -/
theorem fdCompletionFiniteStageLinear
    (l : ℕ) [Fact l.Prime]
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (T : Scheme.{u}) [IsNoetherian T]
    [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (stage : ∀ E : Padic.FiniteCoefficientFields l Ω, FdRationalStageComparison l Ω T E)
    (c : FdCompletionScalarComparison l Ω T stage) :
    ∀ E, (c.family.Φ E).Linear E.val := by sorry

end WeilConjectures
