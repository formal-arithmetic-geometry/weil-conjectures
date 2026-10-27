module

public import Sheaf.Paper.IteratedReturnTransportData

/-! # One-step scalar compatibility and normalization of point sections

Source: blueprint trace-transport, local normalization Steps 4 and 6
(blueprint: lem-trf-point-scalar-single-step-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open IteratedReturnTransport

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (C : IntegralComparisonSystem.{u} l)
  (M : Type u) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
  (ι : E →ₐ[ℚ_[l]] M)
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (j : M →ₐ[ℚ_[l]] L)

/-- The one-step point square uses the very same normalized pullback scalar comparison
as the return square; its inverse sections comparison has the actual unit and tower laws.
Source: the scalar-calculus node's proof Steps 4 and 6, local normalization Steps 8--9
(blueprint: lem-trf-point-scalar-single-step-coherence).

Proof: apply point_automorphism_transport_scalar_extension to geometric Frobenius
on Spec k. Its restriction followed by kappa is the stipulated one-step transport.
Compare its pullback scalar map with integralComparisonScalar by their common
K-flat, quotient-tower and completion-counit normalization. Raw rationalization
and the specified fibre size descent identify the resulting map with
integralComparisonRationalScalar. Conjugate the sections equation by the actual
inverse pointRationalFibreScalarIso to obtain the displayed beta square.
For identity coefficients apply the sections multiplication-unit equation before
rationalization, then the normalized field tensor unit and full faithfulness of
size descent. For successive extensions apply the sections associator equation;
conjugating by the same size-descent counits gives pointFibreFdTensorTower, and
inverting the sections comparisons gives exactly PointScalarNormalization.
These checks are on all integral objects and extend to all raw rational arrows
by tensor linearity; no inverse of an arbitrary object morphism is used. -/
theorem pointScalarSingleStepCoherence
    (hC : IntegralComparisonRealizationCoherence l E M ι C)
    [∀ x : Spec (.of D.k), Invertible (l : (Spec (.of D.k)).residueField x)] :
    RationalPointScalarEquation D l hl E C M ι 1 ∧
      PointScalarNormalization D l hl E M ι L j := by sorry

end WeilConjectures
