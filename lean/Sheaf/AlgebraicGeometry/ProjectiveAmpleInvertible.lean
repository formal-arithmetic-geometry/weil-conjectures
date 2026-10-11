/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.Ample
import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction

/-!
# An ample invertible module from a projective closed immersion

Source: Stacks Project, Properties, Definition 01PS and Lemma 01PU; Constructions,
Definition 01MN and Lemma 01NG (blueprint: lem-weil-pbc-projective-ample-invertible).
-/

universe u

open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Pulling back the Proj twisting sheaf O(1) along the integral-model projection and
then a closed immersion gives an invertible, absolutely ample module. The displayed
opens are exactly the non-vanishing loci of the twice-pulled coordinate sections.
The coordinates are `ULift (Fin (n+1))`, `P^n_ℤ` is `Proj` of the polynomial ring over
`ULift ℤ` with its total-degree grading, `ρ` is `ProjectiveSpace.toProjInt`, the coordinate
`T_k` is `Proj.unitToTwist (isHomogeneous_X _ k)` applied to `1`, and sections are pulled back
by the unit of the chosen tensor-pullback adjunction.
Source: Stacks Project, Properties, Definition 01PS and Lemma 01PU; Constructions,
Definition 01MN and Lemma 01NG (blueprint: lem-weil-pbc-projective-ample-invertible).

Proof:
1. The glued/projective-spectrum twist identification identifies the integral O(1)
   and its coordinates with the glued twist, preserving sections under both pullbacks
   (lem-weil-pbc-projective-space-twist-glued-identification).
2. Standard charts cover projective space, and the pulled coordinate is a free generator
   on each inverse-image chart, proving invertibility
   (lem-weil-pbc-projective-space-standard-charts, def-sc-invertible-module).
3. On that chart its residue-field value is nonzero. Off that chart its ratio to a
   generating coordinate vanishes; locality of the stalk map preserves this vanishing.
   Thus the section's non-vanishing locus equals the chart inverse image
   (lem-weil-pbc-projective-space-standard-charts, def-weil-residue-field).
4. Standard charts over Spec A are affine; their preimages under a closed immersion
   are closed subschemes of affine schemes, hence affine (def-weil-closed-immersion).
5. These n+1 affine opens cover X. Each is quasi-compact, hence so is their finite union
   (lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact). They witness Definition 01PS
   with tensor exponent 1, so L is ample (def-weil-pbc-ample-invertible-module).
-/
theorem projective_closedImmersion_ample_invertible (A : Type u) [CommRing A] (n : ℕ)
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of A))
    (i : X ⟶ ℙ(ULift.{u} (Fin (n + 1)); Spec (CommRingCat.of A))) [IsClosedImmersion i]
    (hi : i ≫ (ℙ(ULift.{u} (Fin (n + 1)); Spec (CommRingCat.of A)) ↘ Spec (.of A)) = f) :
    ∃ hL : ((Scheme.Modules.tensorPullback i).obj
        ((Scheme.Modules.tensorPullback
          (ProjectiveSpace.toProjInt (ULift.{u} (Fin (n + 1))) (Spec (CommRingCat.of A)))).obj
          (Proj.twist (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (n + 1)))
            (ULift.{u} ℤ)) 1))).IsInvertible,
      @Scheme.Modules.IsAmple X ((Scheme.Modules.tensorPullback i).obj
        ((Scheme.Modules.tensorPullback
          (ProjectiveSpace.toProjInt (ULift.{u} (Fin (n + 1))) (Spec (CommRingCat.of A)))).obj
          (Proj.twist (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (n + 1)))
            (ULift.{u} ℤ)) 1))) hL ∧
      CompactSpace X ∧
      ∃ U : ULift.{u} (Fin (n + 1)) → X.Opens,
        (∀ k, (U k : Set X) = Scheme.Modules.nonvanishingLocus
          ((Scheme.Modules.tensorPullback i).obj
            ((Scheme.Modules.tensorPullback
              (ProjectiveSpace.toProjInt (ULift.{u} (Fin (n + 1))) (Spec (CommRingCat.of A)))).obj
              (Proj.twist (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (n + 1)))
                (ULift.{u} ℤ)) 1)))
          (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction i)).unit.app
              ((Scheme.Modules.tensorPullback
                (ProjectiveSpace.toProjInt (ULift.{u} (Fin (n + 1)))
                  (Spec (CommRingCat.of A)))).obj
                (Proj.twist (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (n + 1)))
                  (ULift.{u} ℤ)) 1))).val.app (Opposite.op ⊤)
            (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction
                (ProjectiveSpace.toProjInt (ULift.{u} (Fin (n + 1)))
                  (Spec (CommRingCat.of A))))).unit.app
                (Proj.twist (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (n + 1)))
                  (ULift.{u} ℤ)) 1)).val.app (Opposite.op ⊤)
              ((Proj.unitToTwist (𝒜 := MvPolynomial.homogeneousSubmodule
                  (ULift.{u} (Fin (n + 1))) (ULift.{u} ℤ))
                  (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) k)).app ⊤
                (1 : Γ(Proj (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (n + 1)))
                  (ULift.{u} ℤ)), ⊤)))))) ∧
        (∀ k, IsAffineOpen (U k)) ∧ (⨆ k, U k) = ⊤ := by
  sorry

end AlgebraicGeometry
