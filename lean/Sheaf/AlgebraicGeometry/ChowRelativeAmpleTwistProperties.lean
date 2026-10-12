module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Sheaf.AlgebraicGeometry.Ample


/-! Auxiliary decomposition for Chow relative ampleness. -/

@[expose] public section
universe u
open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra
namespace AlgebraicGeometry
/-- Auxiliary component of the Chow relative ampleness theorem.
Source: Stacks Project, Cohomology of Schemes, Proposition 30.19.1 (Tag 02O5).
Proof in words: this strict component is obtained by the tensor-pullback
functoriality (for the isomorphism component) or by the affine-local standard
chart argument (for the properties component), exactly as in the parent proof.
(blueprint: lem-pc-chow-relative-ample-twist-properties) -/
theorem chow_relative_ample_twist_properties (m : ℕ) (S Z X' : Scheme.{u})
    (g : Z ⟶ S) (π : X' ⟶ Z)
    (j : X' ⟶ ℙ(ULift.{u} (Fin (m + 1)); S))
    [IsProper g] [IsProper π] [IsImmersion j]
    (hj : π ≫ g = j ≫ (ℙ(ULift.{u} (Fin (m + 1)); S) ↘ S)) :
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
  sorry

end AlgebraicGeometry
