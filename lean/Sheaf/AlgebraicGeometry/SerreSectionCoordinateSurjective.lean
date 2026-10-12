/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U3
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist
public import WeilConjectures.Mathlib.RingTheory.MvPolynomial.Homogeneous

import Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Sheaf.AlgebraicGeometry.ProjShiftedFreeTwist
import Sheaf.AlgebraicGeometry.ProjectiveLineTwistExists
import Sheaf.Paper.PQFCohomology
import WeilConjectures.AlgebraicGeometry.Cohomology.Serre
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist

/-! # Eventual surjectivity of coordinate multiplication on twisted sections

Source: Stacks Project, Tag 01YS (4), applied to the locally split coordinate sequence.
(blueprint: lem-sc-p1-section-coordinate-surjective).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

/-- In sufficiently high degrees, every section is a sum of coordinate multiples of
sections in the preceding degree. This asserts no finite generation of a section module.

Source: Stacks Project, Lemma 01YS (4), and the standard two-coordinate sequence on P¹;
https://stacks.math.columbia.edu/tag/01YS.
(blueprint: lem-sc-p1-section-coordinate-surjective).

Proof: the coordinate maps give the sequence
0 → O(-1) → O² → O(1) → 0, with maps t ↦ (-x₁t, x₀t) and
(a,b) ↦ x₀a + x₁b. On D₊(x₀), respectively D₊(x₁), the indicated coordinate
is a unit after trivializing the twists, so this sequence is split exact locally.
Tensoring with G ⊗ O(z) therefore remains exact even when G is not locally free.
The kernel is G ⊗ O(z-1), by the twist tensor addition isomorphisms; the last
map is exactly the sum of the two maps G ◁ Proj.twistMul z, as can be checked
on local homogeneous fractions. Identify these Proj twists with projective-line
and projective-space twists using proj_shifted_free_is_twist and uniqueness of
TwistData. Coherence on this noetherian scheme gives quasi-coherence and finite
presentation. Serre vanishing (01YS (4)) applied to G gives a bound b such that
H¹(G ⊗ O(d)) vanishes for d ≥ b. Choose a natural N ≥ max(0,b+1).
For z ≥ N, the long exact sequence identifies the cokernel of coordinate
multiplication on global sections with a subgroup of H¹(G ⊗ O(z-1)) = 0.
Global sections of the two-fold direct sum are pairs of global sections, giving
the two required preimages. For G = 0 both preimages are zero. The bound excludes
the failure at z = -1 for G = O, where constants do not come from O(-1). -/
theorem serreSectionCoordinateSurjective
    (k : Type u) [Field k]
    (G : (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).Modules)
    (hG : RingedSpace.IsCoherent
      (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).toRingedSpace G) :
    ∃ N : ℕ, ∀ (z : ℤ), (N : ℤ) ≤ z →
      ∀ s : Γ(G ⊗ Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) (z + (1 : ℕ)), ⊤),
      ∃ s₀ s₁ : Γ(G ⊗ Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) z, ⊤),
        s = Scheme.Modules.Hom.app
            (G ◁ Proj.twistMul z (MvPolynomial.X_mem_homogeneousSubmodule_one k (0 : Fin 2)))
            ⊤ s₀ +
          Scheme.Modules.Hom.app
            (G ◁ Proj.twistMul z (MvPolynomial.X_mem_homogeneousSubmodule_one k (1 : Fin 2)))
            ⊤ s₁ := by sorry

end AlgebraicGeometry
