/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist
public import WeilConjectures.Mathlib.RingTheory.MvPolynomial.Homogeneous
import Sheaf.AlgebraicGeometry.ProjShiftedFreeTwist
import WeilConjectures.AlgebraicGeometry.Cohomology.ProjectiveLine

/-! # Finite scalar coordinates for twisted coherent global sections

The finite-dimensional coherent-cohomology step of Stacks Project, Lemma 01YS(3),
including compatibility with the action of constant homogeneous polynomials.
Source: https://stacks.math.columbia.edu/tag/01YS.
(blueprint: lem-sc-p1-twisted-section-finite-coordinates).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry

/-- Twisted coherent global sections on polynomial Proj admit finite scalar coordinates.
Source: Stacks Project, Lemma 01YS(3), and the proof of (5).
(blueprint: lem-sc-p1-twisted-section-finite-coordinates).
Proof: the degree-one standard opens cover Proj, so O(n) is invertible.
Tensoring with it preserves coherence by the local rank-one trivializations.
Use the chart isomorphism to the standard projective line and the twist comparison.
Coherent cohomology is finite-dimensional in degree zero; identify H⁰ with global
sections. Choose a finite basis and take its coordinate additive equivalence.
Multiplication by C(c) on local homogeneous fractions is scalar multiplication by c,
and tensoring with G preserves this formula. The coordinate equivalence therefore
satisfies the displayed formula. The zero sheaf uses r=0, and n=0 uses the same argument.
The equality proof p only transports the target twist along n+0=n. -/
theorem serreTwistedSectionFiniteCoordinates
    (k : Type u) [Field k]
    (G : (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).Modules)
    (hG : RingedSpace.IsCoherent
      (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).toRingedSpace G)
    (n : ℕ) :
    ∃ (r : ℕ) (e :
      Γ(G ⊗ Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) (n : ℤ), ⊤)
        ≃+ (Fin r → k)),
      ∀ (c : k)
        (ha : MvPolynomial.C c ∈ MvPolynomial.homogeneousSubmodule (Fin 2) k 0)
        (s : Γ(G ⊗ Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k)
          (n : ℤ), ⊤))
        (p : G ⊗ Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k)
          ((n : ℤ) + (0 : ℕ)) =
          G ⊗ Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) (n : ℤ)),
        e (Scheme.Modules.Hom.app
          ((G ◁ Proj.twistMul (n : ℤ) ha) ≫ eqToHom p) ⊤ s) = c • e s := by sorry

end AlgebraicGeometry
