/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S9
-/
module

public import Sheaf.Paper.ClosedTestScalarModelDiagrams

/-! # Universal scalar compatibility for derived adjunctions
Source: Stacks Tags 070I, 070Y and 09T5
(blueprint: lem-sfb-closed-test-scalar-universal-coherence). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.ClosedTestScalarModelCoherence
open ClosedTestKInjectiveSectionModels
open ClosedTestDerivedExchangeModel (restrict restrictPush scalarUnit adj pullComp)
variable {Λ S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj S] [IsCommMonObj S]
  (c : Λ ⟶ S) [IsMonHom c]
/-- Universal computation-unit, unit, counit, compositor and exchange equations.
Source: Stacks derived.tex Tags 070I, 070Y, 09T5 and sites-cohomology.tex
Tags 07A6, 0D6D and 0FPI
(blueprint: lem-sfb-closed-test-scalar-universal-coherence).
Proof: use exactSquare_rightDerived_unit for the ordinary commuting direct-image
and scalar square. The computation-unit equation characterizes the forward
comparison uniquely. Transport to section-ring modules using the internal/section
scalar adjunction and the derived pushpull normalization. The ring-sheaf change
adjunction's comparison has the same equation and hence is restrictPush. Apply
its adjunct identity to the identity and to the counit to obtain the unit and
counit clauses. Ordinary pullback/scalar compositors commute by naturality of
pullback from the point. Termwise exact descent gives the derived compositor
clause with its specified factors. Expand exchange as unit, pullback square,
and counit. Move restrictPush across the latter composite by naturality, insert
the counit and compositor equations, then insert the unit equation. This gives
the last displayed square without canceling or inverting restrictPush. -/
theorem closed_test_scalar_universal_coherence : UniversalCoherence c := by sorry

end AlgebraicGeometry.ProEtale.ClosedTestScalarModelCoherence
