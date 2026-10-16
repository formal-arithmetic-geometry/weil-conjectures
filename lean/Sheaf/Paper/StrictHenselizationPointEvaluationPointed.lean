/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Sheaf.Paper.StrictHenselizationPointEvaluation

/-! # Pointedness of colimit evaluation

Source: Stacks Project, Tag 04HX.
(blueprint: lem-weil-pbc-strict-henselization-point-evaluation-pointed).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

set_option maxHeartbeats 800000 in
-- The colimit comparison unfolds the full affine neighborhood diagram.
/-- Evaluation recovers the given geometric point at every chosen neighbourhood.
Source: Stacks Project, Tag 04HX. This is the colimit coprojection equation,
followed by the naturality and triangle identities of Γ and Spec.
(blueprint: lem-weil-pbc-strict-henselization-point-evaluation-pointed). -/
theorem strictHenselizationPointEvaluation_pointed
    {Y : Scheme.{v}} {Ω : Type v} [Field Ω] [IsAlgClosed Ω]
    (barY : Spec (.of Ω) ⟶ Y)
    (j : SmallModel.{v} (strictHenselizationNeighbourhoods barY)) :
    Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation barY)) ≫
      (strictHenselizationCone barY).π.app (op (op j)) ≫
      (Spec (unop ((equivSmallModel.{v}
        (strictHenselizationNeighbourhoods barY)).inverse.obj j).1.left)).isoSpec.inv =
      ((equivSmallModel.{v} (strictHenselizationNeighbourhoods barY)).inverse.obj
        j).2.left := by
  sorry

end AlgebraicGeometry.Scheme
