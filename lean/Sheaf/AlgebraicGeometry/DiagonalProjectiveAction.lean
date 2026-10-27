/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q36
-/
module

public import Sheaf.AlgebraicGeometry.RingDiagonalizableGroup
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod

/-! # Diagonal projective actions over rings

Source: Thomason, Equivariant resolution, linearization, and Hilbert's fourteenth
problem over arbitrary base schemes (1987), Theorem 3.3 and Corollary 3.4(3), p.32;
the split-torus coordinate specialization in the parent node.
(blueprint: def-sfb-diagonal-projective-action).

The predicate below fixes the action by the actual graded coordinate substitution.
Both projections of the affine-base-change comparison are fixed, so the comparison
cannot disguise another action. All equalities are equalities of scheme morphisms.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory MvPolynomial

namespace AlgebraicGeometry.DiagonalProjectiveAction

attribute [instance] MvPolynomial.gradedAlgebra

/-- The existing diagonalizable group for the free character lattice, in Laurent coordinates.
Its basis element indexed by `ULift.up w` is `t^w`.
Source: Thomason (1987), p.32, split-torus specialization; Stacks Tag 022U.
(blueprint: def-sfb-diagonal-projective-action). -/
abbrev torus (A : Type u) [CommRing A] (r : ℕ) : Grp (Over (Spec (.of A))) :=
  ringDiagonalizableGroup A (ULift.{u} (Fin r → ℤ))

/-- Projective space with n+1 homogeneous coordinates, with its existing structure map.
Source: Stacks, Constructions, Tag 01ND, total-degree polynomial Proj.
(blueprint: def-sfb-diagonal-projective-action). -/
def space (A : Type u) [CommRing A] (n : ℕ) : Over (Spec (.of A)) :=
  Over.mk (Proj.projectiveSpaceOverAffineToSpec (ULift.{u} (Fin (n + 1))) A)

/-- The coefficient-fixing substitution `z_i ↦ t^(w_i) z_i` in the Laurent algebra.
Source: Thomason (1987), p.32, split-torus coordinate specialization in the parent node.
(blueprint: def-sfb-diagonal-projective-action). -/
def coaction (A : Type u) [CommRing A] (r n : ℕ)
    (w : ULift.{u} (Fin (n + 1)) → Fin r → ℤ) :
    MvPolynomial (ULift.{u} (Fin (n + 1))) A →+*
      MvPolynomial (ULift.{u} (Fin (n + 1)))
        (AddMonoidAlgebra A (ULift.{u} (Fin r → ℤ))) :=
  MvPolynomial.eval₂Hom
    (MvPolynomial.C.comp (algebraMap A (AddMonoidAlgebra A (ULift.{u} (Fin r → ℤ)))))
    (fun i ↦ MvPolynomial.C (AddMonoidAlgebra.single (ULift.up (w i)) 1) * MvPolynomial.X i)

/-- An action is the diagonal action with weights w when, under the canonical comparison
`Proj C[z] ≅ Spec C ×_Spec A Proj A[z]`, its action map is Proj of the displayed coaction.
The two projection equalities specify that comparison uniquely. The graded lifts have their
entire underlying ring maps specified, including coefficients, not just geometric points.
Source: Thomason (1987), Theorem 3.3 and Corollary 3.4(3), p.32, split-torus specialization;
Stacks, Constructions, polynomial Proj and its affine base change.
(blueprint: def-sfb-diagonal-projective-action). -/
def IsDiagonal (A : Type u) [CommRing A] (r n : ℕ)
    (w : ULift.{u} (Fin (n + 1)) → Fin r → ℤ)
    (a : ModObj (torus A r).X (space A n)) : Prop :=
  ∃ φ ψ : homogeneousSubmodule (ULift.{u} (Fin (n + 1))) A →+*ᵍ
      homogeneousSubmodule (ULift.{u} (Fin (n + 1)))
        (AddMonoidAlgebra A (ULift.{u} (Fin r → ℤ))),
    φ.toRingHom = coaction A r n w ∧
    ψ.toRingHom = MvPolynomial.map
      (algebraMap A (AddMonoidAlgebra A (ULift.{u} (Fin r → ℤ)))) ∧
    ∃ (hφ : HomogeneousIdeal.irrelevant
          (homogeneousSubmodule (ULift.{u} (Fin (n + 1)))
            (AddMonoidAlgebra A (ULift.{u} (Fin r → ℤ)))) ≤
        (HomogeneousIdeal.irrelevant (homogeneousSubmodule (ULift.{u} (Fin (n + 1))) A)).map
          φ)
      (hψ : HomogeneousIdeal.irrelevant
          (homogeneousSubmodule (ULift.{u} (Fin (n + 1)))
            (AddMonoidAlgebra A (ULift.{u} (Fin r → ℤ)))) ≤
        (HomogeneousIdeal.irrelevant (homogeneousSubmodule (ULift.{u} (Fin (n + 1))) A)).map
          ψ),
      ∃ e : Proj.projectiveSpaceOverAffine (ULift.{u} (Fin (n + 1)))
          (AddMonoidAlgebra A (ULift.{u} (Fin r → ℤ))) ≅
          ((torus A r).X ⊗ space A n).left,
        e.hom ≫ (fst (torus A r).X (space A n)).left =
          Proj.projectiveSpaceOverAffineToSpec (ULift.{u} (Fin (n + 1)))
            (AddMonoidAlgebra A (ULift.{u} (Fin r → ℤ))) ∧
        e.hom ≫ (snd (torus A r).X (space A n)).left = Proj.map ψ hψ ∧
        e.hom ≫ a.smul.left = Proj.map φ hφ

end AlgebraicGeometry.DiagonalProjectiveAction
