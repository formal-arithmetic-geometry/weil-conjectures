/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K4
-/
module

public import Sheaf.Paper.ScalarFibreComponentData

/-! # Objectwise scalar fibre maps before naturality and coherence -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option genCtorIdx false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct ChangeOfRings
namespace AlgebraicGeometry.Scheme.AdicFibreComparison
open ContinuousRational AlgebraicGeometry.ProEtale

variable {k : Type u} [Field k] (l : ℕ) [Fact l.Prime] [Fact (IsUnit (l : k))]
  (R : ContinuousRational.Family.{u} l)

/-- The normalized objectwise scalar maps satisfy the tensor and mixed equations.
Source: BS 6.8.14--6.8.15; Stacks 03Q1(3).
(blueprint: lem-per-scalar-fibre-coherence).

Proof: At finite quotient level, identity scalar extension removes the tensor factor 1.
For successive extensions both routes on a nested pure tensor multiply its two scalar
coefficients. The finite stalk scalar theorem and the realization scalar unit and tower
comparisons identify these routes with the specified raw unit and associator. Their
restrictions to the full heart are exactly scalarHeartUnit and scalarHeartComp. For the
mixed square, the normalized pullback germ equation sends a pulled germ to the original
germ; applying scalar extension before or after gives the same scalar tensor of that
germ. The realization mixed comparison fixes the underlying map to scalarHeartMixed.
These equalities commute with quotient projections. Joint monicity passes them to inverse
limits, and the completion-cone equation passes them through the inverse integral
comparison. Localizing proves the same equalities on rational pure tensors. Such tensors
span, so the equations hold on every fibre. Alternatively the unit-normalization formulas
compute them on every presented sheaf germ. The normalized pullback and scalar chart
formulas identify the result with the original point functors. Repeated coefficient fields,
zero rank and empty schemes are included; no quotient coefficient map is assumed flat. -/
theorem scalar_fibre_coherence (ω : Fibres (k := k) l R)
    (α : NormalizedPullback l R ω) (d : ScalarFibreComponents l R ω) :
    ScalarFibreCoherence l R ω α d := by sorry

end AlgebraicGeometry.Scheme.AdicFibreComparison
