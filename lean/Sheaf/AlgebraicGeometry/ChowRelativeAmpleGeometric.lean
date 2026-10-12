module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import Sheaf.AlgebraicGeometry.Morphisms.Projective

@[expose] public section
universe u
open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra
namespace AlgebraicGeometry

/-- Geometric consequences of the Chow immersion.

Source: Stacks Project, Cohomology of Schemes, Proposition 30.19.1 (Tag 02O5).
Proof in words: properness of `g` and `π` is stable under composition, and the
projective-space structure map is separated.  Hence the proper immersion `j`
has closed image, so the closed-image criterion makes `j` a closed immersion;
properness also supplies the quasi-compactness required for projectivity of
`π ≫ g`.  Base-changing `j` along `g` and composing with the graph of `π`
gives `ProjectiveSpace.liftBaseChange π j hj`; the diagonal of the proper map
`g` is closed, so this composite is a closed immersion.  The same properness
and quasi-compactness argument then makes `π` projective.

(blueprint: lem-pc-chow-relative-ample-geometric) -/
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
  · exact { exists_closedImmersion := ⟨m, j, inferInstance, hj.symm⟩ }
  · exact { exists_closedImmersion :=
      ⟨m, ProjectiveSpace.liftBaseChange π j hj, inferInstance,
        ProjectiveSpace.liftBaseChange_over π j hj⟩ }

end AlgebraicGeometry
