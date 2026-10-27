/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.PbcDescentInterfaces

/-! # Normalized completed-pullback coefficient families

Source: blueprint main-20261015, proper base change, order 1312, final paragraph.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe w u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
variable (l : ℕ) [Fact l.Prime] (Ω : Type w)
  [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

variable {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
  [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
  [iX : Fact (∀ t : X, IsUnit (l : X.presheaf.stalk t))]
  [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))]
  [iY : Fact (∀ t : Y, IsUnit (l : Y.presheaf.stalk t))]

/-- The actual rationalized completed-pullback operations form a coherent exact family,
with the prescribed normalized scalar comparisons at every pair of stages.
Source: blueprint main-20261015, order 1312, final paragraph; rational transport
and finite scalar extension (blueprint: lem-weil-pbc-pullback-coherent-family).

Proof: the actual completed operation is ordinary derived pullback followed by
the completion reflector. Ordinary derived pullback is the left adjoint of the
exact derived direct image. The derived-unit and derived-counit normalizations
fix its shift and make that adjunction commute with shifts, so it is exact.
The complete-object subcategory is triangulated: use the exact completion data
and its unit-locus characterization. Its reflector is exact, with the shift
compatible with its reflection unit. Uniqueness in pbcActualCompletionShift_exists
identifies this shift with the recorded actual completion shift. Thus completed
pullback preserves the required distinguished triangles; alternatively use
completedPullback_preserves_shifts_distinguished on complete inputs, with the
same unit normalization. Restrict the actual operation to the full bounded
constructible complete subcategories using pres. The full inclusions reflect
its exactness, with the integral shift inherited by Functor.CommShift.ofComp. Its additive linear
maps extend to the raw
scalar localization. For E ≤ F conjugate the localized ambient scalar-operation
comparison by pbcScalarIntegralComparison at its two endpoints; for pullback take
the inverse comparison. Equivalently lift the integral comparisons uniquely
through the fully faithful whiskering functor for rational localization.
The unique finite-quotient characterization identifies
the small-field coefficient map with the canonical completed map. Invert the component equation
pbcScalarCompletedPull_coefficients, using
functoriality of mapIso and the iso cancellation laws, to obtain the tower
equation in the beta orientation. That ambient equation then gives the stage-system associator
equation after
restriction and localization, including repeated fields. The unit equation follows
by cancellation from this equation at repeated stages. The integral comparison
commutes with shifts by pbcScalarOperations_shift; localization preserves that
identity on pure tensors, hence on all rational morphisms. The raw and canonical ambient tensor
shifts agree by uniqueness of the
left-adjoint shift compatible with scalar restriction. Full faithfulness of the
integral inclusion reflects the comparison's shift equation. The normalized
integral localization squares uniquely fix the rational stage shifts, and the
scalar/integral comparisons commute with shifts. Whiskering with localization
therefore reflects the beta shift equation on all rational objects, since every
one is an integral representative. Give each functor this uniquely normalized
localized shift structure. Integral exactness and the characterization of rational
distinguished triangles as integral image triangles prove stage exactness. Finally
the two conjugating comparisons cancel to give precisely the BetaSpec formula. -/
theorem pbcPullbackCoherentFamily (f : X ⟶ Y)
    (pres : ∀ (E : Padic.FiniteCoefficientFields l Ω)
      (K : pbcIntegralStage l Ω Y E),
      PbcIsBoundedConstructibleComplete X (pbcStageDatum.{u} l Ω E)
        ((pbcActualCompletedPull f (pbcStageDatum.{u} l Ω E)).obj K.obj)) :
    ∃ F : StageSystem.CoherentExactMorphism
      (pbcScalarSystem l Ω Y dY.out iY.out)
      (pbcScalarSystem l Ω X dX.out iX.out),
      (∀ E : Padic.FiniteCoefficientFields l Ω,
        F.base.Φ E = pbcDescentPullback l Ω f pres E) ∧
      PbcPullbackBetaSpec l Ω f pres F.base := by
  sorry

end AlgebraicGeometry.Scheme
