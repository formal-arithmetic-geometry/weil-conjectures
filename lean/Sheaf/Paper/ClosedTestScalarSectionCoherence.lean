/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S9
-/
module

public import Sheaf.Paper.ClosedTestScalarModelDiagrams
import Sheaf.Paper.ClosedTestScalarSectionSquares

/-! Section evaluation compatibility for scalar restriction, split from the combined theorem.
Source: Stacks sites-cohomology.tex Tags 07A6, 0D6F and 0FPI
(blueprint: lem-sfb-closed-test-scalar-section-coherence).
The proof is the degreewise section identity transported through the universal
right-derived units and localization comparisons. -/

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

/-- Assemble section coherence using the universal section comparison unit equation.
Source: Stacks Tag 070Y and sites-cohomology.tex Tag 0D6F
(blueprint: lem-sfb-closed-test-scalar-section-coherence).
The first clause is rightDerivedFunctorUnitQ_rightDerivedPullback_app with the
identity ordinary section transformation. The other three are the section squares. -/
theorem closed_test_scalar_section_coherence : SectionCoherence c := by
  refine ⟨?_, closed_test_scalar_section_squares c⟩
  intro X W P
  have h := Functor.rightDerivedFunctorUnitQ_rightDerivedPullback_app
    (restriction c X) (F := evaluation S W) (F' := evaluation Λ W) (𝟙 _) P
  rw [NatTrans.mapHomologicalComplex_id, NatTrans.id_app] at h
  erw [CategoryTheory.Functor.map_id, Category.id_comp] at h
  exact h

end AlgebraicGeometry.ProEtale.ClosedTestScalarModelCoherence
