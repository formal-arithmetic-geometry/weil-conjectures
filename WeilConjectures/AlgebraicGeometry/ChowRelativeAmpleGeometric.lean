/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective


public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace

@[expose] public section
universe u
open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra
namespace AlgebraicGeometry

/-- Geometric consequences of the Chow immersion.

The immersions `j` and `ProjectiveSpace.liftBaseChange π j hj` are closed immersions, and
`π ≫ g` and `π` are projective (Stacks, Tag 02O5). -/
theorem chow_relative_ample_geometric (m : ℕ) (S Z X' : Scheme.{u})
    (g : Z ⟶ S) (π : X' ⟶ Z)
    (j : X' ⟶ ℙ(ULift.{u} (Fin (m + 1)); S))
    [IsProper g] [IsProper π] [IsImmersion j]
    (hj : π ≫ g = j ≫ (ℙ(ULift.{u} (Fin (m + 1)); S) ↘ S)) :
    IsClosedImmersion j ∧ IsProjective (π ≫ g) ∧
      IsClosedImmersion (ProjectiveSpace.liftBaseChange π j hj) ∧ IsProjective π := by
  have : IsProper (j ≫ (ℙ(ULift.{u} (Fin (m + 1)); S) ↘ S)) := by
    rw [← hj]
    infer_instance
  have : IsProper j := IsProper.of_comp j (ℙ(ULift.{u} (Fin (m + 1)); S) ↘ S)
  have : IsClosedImmersion j :=
    IsClosedImmersion.of_isPreimmersion j j.isClosedMap.isClosed_range
  have : IsClosedImmersion (ProjectiveSpace.liftBaseChange π j hj) := inferInstance
  refine ⟨inferInstance, ?_, inferInstance, ?_⟩
  · exact { exists_isClosedImmersion :=
      ⟨ULift.{u} (Fin (m + 1)), inferInstance, j, inferInstance, hj.symm⟩ }
  · exact { exists_isClosedImmersion :=
      ⟨ULift.{u} (Fin (m + 1)), inferInstance, ProjectiveSpace.liftBaseChange π j hj, inferInstance,
        ProjectiveSpace.liftBaseChange_over π j hj⟩ }

end AlgebraicGeometry
