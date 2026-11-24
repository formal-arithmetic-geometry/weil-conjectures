/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective


public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.Ample
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.ChowRelativeAmpleGeometric
import WeilConjectures.AlgebraicGeometry.ChowRelativeAmpleTwist

/-!
# Chow immersion and relative ampleness

## References

* Stacks Project, Tag 02O5
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry

set_option linter.unusedVariables false in
/-- The Chow immersion is closed and its pulled-back twisting module is relatively ample
(Stacks, Tag 02O5). -/
theorem chow_relative_ample (m : ℕ) (S Z X' : Scheme.{u})
    (g : Z ⟶ S) (π : X' ⟶ Z)
    (j : X' ⟶ ℙ(ULift.{u} (Fin (m + 1)); S))
    [IsProper g] [IsProper π] [IsImmersion j]
    (hj : π ≫ g = j ≫ (ℙ(ULift.{u} (Fin (m + 1)); S) ↘ S)) :
    IsClosedImmersion j ∧ IsProjective (π ≫ g) ∧
      IsClosedImmersion (ProjectiveSpace.liftBaseChange π j hj) ∧ IsProjective π ∧
      Nonempty (((Scheme.Modules.tensorPullback j).obj
          ((Scheme.Modules.tensorPullback (ProjectiveSpace.toProjInt
            (ULift.{u} (Fin (m + 1))) S)).obj
            (Proj.twist (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (m + 1)))
              (ULift.{u} ℤ)) 1))) ≅
        ((Scheme.Modules.tensorPullback (ProjectiveSpace.liftBaseChange π j hj)).obj
            ((Scheme.Modules.tensorPullback (ProjectiveSpace.toProjInt
              (ULift.{u} (Fin (m + 1))) Z)).obj
              (Proj.twist (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (m + 1)))
                (ULift.{u} ℤ)) 1)))) ∧
      ∃ hL : ((Scheme.Modules.tensorPullback j).obj
          ((Scheme.Modules.tensorPullback (ProjectiveSpace.toProjInt
            (ULift.{u} (Fin (m + 1))) S)).obj
            (Proj.twist (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (m + 1)))
              (ULift.{u} ℤ)) 1))).IsInvertible,
        (∀ V : S.Opens, IsAffineOpen V →
          ∃ hV : ((Scheme.Modules.tensorPullback ((π ≫ g) ⁻¹ᵁ V).ι).obj
              ((Scheme.Modules.tensorPullback j).obj
              ((Scheme.Modules.tensorPullback (ProjectiveSpace.toProjInt
                (ULift.{u} (Fin (m + 1))) S)).obj
                (Proj.twist (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (m + 1)))
                  (ULift.{u} ℤ)) 1)))).IsInvertible,
            @Scheme.Modules.IsAmple ((π ≫ g) ⁻¹ᵁ V).toScheme
              ((Scheme.Modules.tensorPullback ((π ≫ g) ⁻¹ᵁ V).ι).obj
                  ((Scheme.Modules.tensorPullback j).obj
                  ((Scheme.Modules.tensorPullback (ProjectiveSpace.toProjInt
                    (ULift.{u} (Fin (m + 1))) S)).obj
                    (Proj.twist (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (m + 1)))
                      (ULift.{u} ℤ)) 1)))) hV) ∧
        (∀ W : Z.Opens, IsAffineOpen W →
          ∃ hW : ((Scheme.Modules.tensorPullback (π ⁻¹ᵁ W).ι).obj
              ((Scheme.Modules.tensorPullback j).obj
              ((Scheme.Modules.tensorPullback (ProjectiveSpace.toProjInt
                (ULift.{u} (Fin (m + 1))) S)).obj
                (Proj.twist (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (m + 1)))
                  (ULift.{u} ℤ)) 1)))).IsInvertible,
            @Scheme.Modules.IsAmple (π ⁻¹ᵁ W).toScheme
              ((Scheme.Modules.tensorPullback (π ⁻¹ᵁ W).ι).obj
                  ((Scheme.Modules.tensorPullback j).obj
                  ((Scheme.Modules.tensorPullback (ProjectiveSpace.toProjInt
                    (ULift.{u} (Fin (m + 1))) S)).obj
                    (Proj.twist (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (m + 1)))
                      (ULift.{u} ℤ)) 1)))) hW) := by
  have hA := chow_relative_ample_geometric m S Z X' g π j hj
  have hB := chow_relative_ample_twist m S Z X' g π j hj
  exact ⟨hA.1, hA.2.1, hA.2.2.1, hA.2.2.2, hB⟩

end AlgebraicGeometry
