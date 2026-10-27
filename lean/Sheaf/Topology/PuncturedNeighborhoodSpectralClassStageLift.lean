/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J8
-/
module
public import Sheaf.Topology.PuncturedNeighborhoodInverseLimit
public import Sheaf.Topology.OpenSystemColimitCohomologyComparison
import Sheaf.Topology.SpectralLimitCohomologyClassLift
import Sheaf.Topology.CanonicalCohomologyPullbackNormalization
/-! # Stage representation for the constructed punctured restriction system
Source: Stacks Project, Cohomology, Tag 0A37.
(blueprint: lem-weil-pbc-punctured-spectral-class-stage-lift)
-/
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace TopCat
/-- A class in the colimit coefficient sheaf comes from cohomology of one stage.
Source: Stacks Project, Cohomology, Tag 0A37, applied to punctured compact-open stages.
(blueprint: lem-weil-pbc-punctured-spectral-class-stage-lift)

Proof: Use the reverse-inclusion compact-open neighborhood index. Its punctured stages
are spectral and the inclusions spectral. The compatible-tuple limit and initial topology
are puncturedStageProjection_limit and puncturedStageProjection_initial. The restriction
presentation supplies the actual stage sheaves, transition maps, constant limit coefficient
functor and unit compatibility. Use objectCohomologyPullback_normalized for each projection.
Apply spectralLimit_cohomology_class_lift. This conclusion concerns only stage cohomology
and the coefficient colimit, not ambient object cohomology or the canonical cocone leg. -/
theorem punctured_spectral_class_stage_lift
    {T : Type u} [TopologicalSpace T] [SpectralSpace T]
    (Z : Set T) (hZ : IsClosed Z) (hU : IsCompact Zᶜ)
    (A : CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}) (q : ℕ)
    (y : CategoryTheory.Sheaf.H' (colimit (OpenSystem.coefficients
      (I := puncturedNeighborhoodIndex Z) (puncturedGeneralizations Z) A)) q ⊤) :
    ∃ (i : puncturedNeighborhoodIndex Z)
      (x : CategoryTheory.Sheaf.H' (OpenSystem.stageSheaf (puncturedStageOpen Z hZ) A i) q ⊤),
      (TopCat.Sheaf.spectralLimitCohomologyMap
        (OpenSystem.inclusionOfLE (puncturedStageOpen_contains Z hZ i))
        (objectCohomologyPullback
          (OpenSystem.inclusionOfLE (puncturedStageOpen_contains Z hZ i)))
        ((OpenSystem.adjunction
          (OpenSystem.inclusionOfLE (puncturedStageOpen_contains Z hZ i))).homEquiv _ _
          ((OpenSystem.coefficientIso (puncturedStageOpen Z hZ) (puncturedGeneralizations Z)
            (puncturedStageOpen_contains Z hZ) A i).inv ≫
              colimit.ι (OpenSystem.coefficients (I := puncturedNeighborhoodIndex Z)
                (puncturedGeneralizations Z) A) i)) q).hom x = y := by sorry
end TopCat
