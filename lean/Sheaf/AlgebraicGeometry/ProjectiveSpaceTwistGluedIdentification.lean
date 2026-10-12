/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
import Sheaf.AlgebraicGeometry.ProjectiveSpaceTwistingSheafCharts
import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules

/-!
# Identification of the glued twist with the Serre twist

Source: Stacks Project, Constructions, Section 01MM and Lemma 01MS;
Sheaves, Section 00AK and Lemma 00AL
(blueprint: lem-weil-pbc-projective-space-twist-glued-identification).

`P = Proj ℤ[T_k : k ∈ n]` is the integral model `Proj (homogeneousSubmodule n (ULift ℤ))`.
The glued module `𝒪_P(1)` of def-pc-projective-space-twist (A = ℤ, d = 1) is its recorded
declaration `ProjectiveSpace.twist n (Spec ℤ) 1` on `ℙ(n; Spec ℤ)`, carried to `P` along the
projection `ProjectiveSpace.toProjInt` (an isomorphism, the base being `Spec ℤ`) by
`Scheme.Modules.pushforward`. Its chart bases are `e_i = T^gl_i|_{U_i}` and its global
coordinate sections are `T^gl_k = ProjectiveSpace.twistOneSection n (Spec ℤ) k`, which satisfy
the transition rule `e_i = (T_i/T_j) e_j` and `T^gl_k|_{U_i} = (T_k/T_i) e_i`
(`ProjectiveSpace.pullbackSection_twistOneSection_map_eq_smul`).
-/

@[expose] public section

universe u

open CategoryTheory
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The glued O(1) has a unique isomorphism to the Serre twist preserving its chart bases;
the isomorphism carries the glued coordinate sections to the polynomial coordinate sections.
Source: Stacks Project, Constructions 01MS and Sheaves 00AL
(blueprint: lem-weil-pbc-projective-space-twist-glued-identification).

Proof: (1) Relabel the finite nonempty variable set as {0,...,N}. The polynomial Proj,
Serre twist, and polynomial coordinate sections are precisely those of
lem-weil-pbc-projective-space-twisting-sheaf-charts. The bases of
def-pc-projective-space-twist identify the glued module with the module L in clause (v).
The prescribed restrictions of the glued coordinate sections identify them with the x_k
in that clause, since the standard opens cover Proj and sections are determined locally.
(2) Apply clause (v) of lem-weil-pbc-projective-space-twisting-sheaf-charts: on each chart
send a e_i to a T_i. These local isomorphisms agree on overlaps by the transition rule
and glue, as do their inverses (lem-pur-sheaf-hom-is-sheaf, Stacks 00AL). A map preserving
each basis is determined on every chart, giving uniqueness. The image of each glued
coordinate section has restriction (T_k/T_i) T_i = T_k, so is T_k globally. -/
theorem existsUnique_polynomial_twist_glued_identification
    (n : Type u) [Finite n] [Nonempty n] :
    ∃! θ : (Scheme.Modules.pushforward
          (ProjectiveSpace.toProjInt n (Spec (CommRingCat.of (ULift.{u} ℤ))))).obj
          (ProjectiveSpace.twist n (Spec (CommRingCat.of (ULift.{u} ℤ))) 1) ≅
        Proj.twist (MvPolynomial.homogeneousSubmodule n (ULift.{u} ℤ)) 1,
      (∀ i : n,
        θ.hom.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule n (ULift.{u} ℤ))
            (MvPolynomial.X i))
          ((ProjectiveSpace.twist n (Spec (CommRingCat.of (ULift.{u} ℤ))) 1).presheaf.map
            (homOfLE (le_top :
              ProjectiveSpace.toProjInt n (Spec (CommRingCat.of (ULift.{u} ℤ))) ⁻¹ᵁ
                Proj.basicOpen (MvPolynomial.homogeneousSubmodule n (ULift.{u} ℤ))
                  (MvPolynomial.X i) ≤ ⊤)).op
            (ProjectiveSpace.twistOneSection n (Spec (CommRingCat.of (ULift.{u} ℤ))) i)) =
          Proj.twistPowSection 1 (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) i)) ∧
      (∀ k : n,
        θ.hom.app ⊤
            (ProjectiveSpace.twistOneSection n (Spec (CommRingCat.of (ULift.{u} ℤ))) k) =
          (Proj.unitToTwist (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) k)).app ⊤
            (1 : Γ(Proj (MvPolynomial.homogeneousSubmodule n (ULift.{u} ℤ)), ⊤))) := by
  sorry

end AlgebraicGeometry.Proj
