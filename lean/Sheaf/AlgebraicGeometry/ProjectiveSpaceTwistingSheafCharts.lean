/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Sheaf.AlgebraicGeometry.Ample

/-!
# The twisting sheaf on the standard charts of integral projective space

Source: Stacks Project, Constructions, Tags 01MN, 01M7, 01MS, 01MB, 01NG, 01MV
(blueprint: lem-weil-pbc-projective-space-twisting-sheaf-charts).
-/

@[expose] public section

open CategoryTheory Opposite
open scoped AlgebraicGeometry.Scheme.Modules
namespace AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 800000 in
-- Comparing the section types of the transported twist unfolds the Proj sheaf construction.
/-- All five clauses of the integral projective-space chart statement.
Source: Stacks Project, Constructions, Tags 01MN, 01M7, 01MS, 01MB, 01NG, 01MV;
blueprint def-pc-projective-space-twist for the glued module comparison
(blueprint: lem-weil-pbc-projective-space-twisting-sheaf-charts).

Proof:
1. The variables generate the irrelevant ideal, hence their standard opens cover
   (prop-nagata-proj-standard-open). Each degree-one variable gives the canonical affine
   chart. Apply lem-weil-pbc-dehomogenization-polynomial-ring for its coordinate ring.
2. By def-weil-pbc-proj-twisting-sheaf and lem-weil-pbc-proj-graded-module-sheaf-exists,
   sections of O(1) on D₊(g) are degree-one fractions, restriction is localization, and
   the coordinate section T_l restricts to T_l/1.
3. On a basic open contained in D₊(T_j), T_j becomes a unit. Multiplication by T_j
   bijects degree-zero and degree-one fractions, with inverse division by T_j.
   These basic opens form a basis; pass to stalks and use lem-weil-pbc-module-iso-on-stalks
   to obtain the specified module trivialization.
4. The trivializations cover and the twist is quasi-coherent, hence it is invertible
   (def-sc-invertible-module).
5. Multiplication of fractions gives T_l/1 = (T_l/T_j)(T_j/1), including l = j.
6. In the frame T_k the germ of T_j is outside the maximal ideal times the stalk exactly
   when T_j/T_k is outside the maximal ideal. Its basic open is D₊(T_j) intersect D₊(T_k)
   (lem-weil-pbc-basic-open-function, lem-weil-pbc-proj-basic-open-intersection).
   The chart cover gives the nonvanishing-locus identity globally.
7. Send the glued frame e_j to T_j. The transition identity from step 5 makes the local
   isomorphisms agree. Glue them and their inverses using lem-pur-sheaf-hom-is-sheaf.
   Frames determine each local map, giving uniqueness. The glued coordinate x_l maps
   locally to (T_l/T_j)T_j = T_l and thus maps to T_l globally.
-/
theorem projectiveSpace_twistingSheaf_charts (n : ℕ) :
    (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{0} ℤ)) 1).IsInvertible ∧
    (⨆ j : Fin (n + 1), Proj.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{0} ℤ)) (MvPolynomial.X j)) = ⊤ ∧
    (∀ j : Fin (n + 1), IsIso (Proj.basicOpenToSpec
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{0} ℤ)) (MvPolynomial.X j))) ∧
    (∀ j : Fin (n + 1), ∃ E : MvPolynomial {l : Fin (n + 1) // l ≠ j} (ULift.{0} ℤ) ≃ₐ[ULift.{0} ℤ]
      HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{0} ℤ))
        (MvPolynomial.X j), ∀ l : {l : Fin (n + 1) // l ≠ j},
        E (MvPolynomial.X l) = MvPolynomial.awayXRatio (ULift.{0} ℤ) j l.1) ∧
    (∀ j : Fin (n + 1), IsIso ((Scheme.Modules.restrictFunctor
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{0} ℤ))
        (MvPolynomial.X j)).ι).map
          (Proj.unitToTwist
          (𝒜 := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{0} ℤ))
          (MvPolynomial.X_mem_homogeneousSubmodule_one (ULift.{0} ℤ) j)))) ∧
    (∀ j : Fin (n + 1), Scheme.Modules.nonvanishingLocus
      (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{0} ℤ)) 1)
      ((Proj.unitToTwist
          (𝒜 := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{0} ℤ))
          (MvPolynomial.X_mem_homogeneousSubmodule_one (ULift.{0} ℤ) j)).app ⊤
        (1 : Γ(Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{0} ℤ)), ⊤))) =
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{0} ℤ))
        (MvPolynomial.X j) : Set (Proj
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{0} ℤ))))) ∧
    (∀ j l : Fin (n + 1),
      (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{0} ℤ)) 1).presheaf.map
        (homOfLE (le_top : Proj.basicOpen
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{0} ℤ))
            (MvPolynomial.X j) ≤ ⊤)).op
        ((Proj.unitToTwist
          (𝒜 := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{0} ℤ))
          (MvPolynomial.X_mem_homogeneousSubmodule_one (ULift.{0} ℤ) l)).app ⊤
          (1 : Γ(Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{0} ℤ)), ⊤))) =
      Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{0} ℤ))
        (MvPolynomial.X j) (MvPolynomial.awayXRatio (ULift.{0} ℤ) j l) •
      (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{0} ℤ)) 1).presheaf.map
        (homOfLE (le_top : Proj.basicOpen
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{0} ℤ))
            (MvPolynomial.X j) ≤ ⊤)).op
        ((Proj.unitToTwist
          (𝒜 := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{0} ℤ))
          (MvPolynomial.X_mem_homogeneousSubmodule_one (ULift.{0} ℤ) j)).app ⊤
          (1 : Γ(Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{0} ℤ)), ⊤)))) ∧
    ∃! θ : (Scheme.Modules.pushforward
          (ProjectiveSpace.toProjInt (Fin (n + 1)) (Spec (CommRingCat.of (ULift.{0} ℤ))))).obj
          (ProjectiveSpace.twist (Fin (n + 1)) (Spec (CommRingCat.of (ULift.{0} ℤ))) 1) ≅
        Proj.twist (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{0} ℤ)) 1,
      (∀ i : Fin (n + 1),
        θ.hom.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{0} ℤ))
            (MvPolynomial.X i))
          ((ProjectiveSpace.twist (Fin (n + 1))
              (Spec (CommRingCat.of (ULift.{0} ℤ))) 1).presheaf.map
            (homOfLE (le_top :
              ProjectiveSpace.toProjInt (Fin (n + 1)) (Spec (CommRingCat.of (ULift.{0} ℤ))) ⁻¹ᵁ
                Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{0} ℤ))
                  (MvPolynomial.X i) ≤ ⊤)).op
            (ProjectiveSpace.twistOneSection (Fin (n + 1))
              (Spec (CommRingCat.of (ULift.{0} ℤ))) i)) =
          Proj.twistPowSection 1 (MvPolynomial.X_mem_homogeneousSubmodule_one (ULift.{0} ℤ) i)) ∧
      (∀ k : Fin (n + 1),
        θ.hom.app ⊤
            (ProjectiveSpace.twistOneSection (Fin (n + 1))
              (Spec (CommRingCat.of (ULift.{0} ℤ))) k) =
          (Proj.unitToTwist
          (𝒜 := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{0} ℤ))
          (MvPolynomial.X_mem_homogeneousSubmodule_one (ULift.{0} ℤ) k)).app ⊤
            (1 : Γ(Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{0} ℤ)), ⊤))) := by
  sorry

end AlgebraicGeometry
