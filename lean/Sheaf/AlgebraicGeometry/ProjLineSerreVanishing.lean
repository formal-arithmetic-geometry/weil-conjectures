/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R3
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.Mathlib.RingTheory.MvPolynomial.Homogeneous

import Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Sheaf.AlgebraicGeometry.ProjShiftedFreeTwist
import Sheaf.AlgebraicGeometry.ProjectiveLineTwistExists
import WeilConjectures.AlgebraicGeometry.Cohomology.Serre
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist

/-! # Serre vanishing for the polynomial Proj model of the projective line

Source: Stacks Project, Tag 01YS (4), with twists as in Tag 01MN.
(blueprint: lem-sc-p1-proj-serre-h1-vanishing).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Serre vanishing in degree one, expressed for polynomial Proj twists.

Source: Stacks Project, Tag 01YS (4), and Tag 01MN (1),(2).
(blueprint: lem-sc-p1-proj-serre-h1-vanishing).

Proof: Polynomial Proj is the projective line over k. Identify it with the relative
projective line using the standard affine charts, sending their parameters to x1/x0
and x0/x1. The comparison is a scheme isomorphism. The degree-d fractions of the
shifted free polynomial module have generators xi^d on D+(xi), with transition
x0^d = (x0/x1)^d x1^d, including negative d because xi is invertible there.
Thus Proj.twist d is the pullback of the relative twist d, by uniqueness of the
module glued from these generators. The comparison preserves coherence and sheaf
cohomology. Over the field k the line is noetherian; a coherent module is
quasi-coherent and finitely presented. Apply Serre vanishing on relative projective
space to the transported G in degree one, and transport the resulting zero groups
back through the twist and tensor comparison isomorphisms. This gives an integer
bound b independent of d. For G=0 all cohomology groups are zero and b=0 works.
-/
theorem exists_subsingleton_H_one_tensor_proj_twist
    (k : Type u) [Field k]
    (G : (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).Modules)
    (hG : RingedSpace.IsCoherent
      (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).toRingedSpace G) :
    ∃ b : ℤ, ∀ d : ℤ, b ≤ d →
      Subsingleton ((G ⊗ Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) d).H 1) := by
  sorry

end AlgebraicGeometry
