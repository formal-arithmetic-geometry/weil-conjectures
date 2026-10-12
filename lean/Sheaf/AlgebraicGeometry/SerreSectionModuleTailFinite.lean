/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P3
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist
public import WeilConjectures.Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Finiteness.Defs

import Sheaf.AlgebraicGeometry.Modules.FiniteLocallyFreeTensorExact
import Sheaf.AlgebraicGeometry.ProjShiftedFreeTwist
import Sheaf.AlgebraicGeometry.ProjectiveLineTwistExists
import Sheaf.Paper.PQFCohomology
import WeilConjectures.AlgebraicGeometry.Cohomology.Serre
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist

/-! # SerreSectionModuleTailFinite

Intermediate step for finite generation of graded sections. -/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The span of all sufficiently high section degrees is finitely generated.
This asserts only tail finiteness, with no finiteness assertion about the lower degrees.

Source: Stacks Project, Lemma 01YS(5), first three paragraphs of its proof;
https://stacks.math.columbia.edu/tag/01YS.
(blueprint: lem-sc-p1-section-module-tail-finite).
Proof: use the finite twist quotient E → G with coherent kernel K. Identify Proj twists
with the standard projective-line twists using proj_shifted_free_is_twist and uniqueness
of TwistData. Coherence on the noetherian scheme gives quasi-coherence and finite
presentation, so the quoted twist quotient and Serre vanishing apply. Tensor the exact
sequence with O(d); invertibility preserves exactness. Choose N ≥ 0 so H¹(K(d)) vanishes
for every d ≥ N. The cohomology exact sequence then makes Γ(E(d)) → Γ(G(d)) surjective.
The sections of the finite sum E are the homogeneous pieces of a finite sum of shifts
of S, by twist tensor addition and the monomial H⁰ calculation. These identifications
commute with homogeneous multiplication. The tail of that graded free module is a
submodule, since polynomial degrees are nonnegative; it is finite by noetherianity of S.
Map its degree-d elements through the section quotient and φ(d) inverse into M. The
compatibility hφ makes this map S-linear and its image is exactly the span in the
conclusion, so that span is finite. For E=0, take its empty generating set. -/
theorem serreSectionModuleTailFinite
    (k : Type u) [Field k]
    (G : (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).Modules)
    (hG : RingedSpace.IsCoherent
      (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).toRingedSpace G)
    (M : ModuleCat.{u} (MvPolynomial (Fin 2) k))
    (𝓜 : ℤ → AddSubgroup M)
    (hsmul : ∀ (e : ℕ) (z : ℤ) (a : MvPolynomial (Fin 2) k) (y : M),
      a ∈ MvPolynomial.homogeneousSubmodule (Fin 2) k e → y ∈ 𝓜 z → a • y ∈ 𝓜 (e + z))
    (φ : ∀ z : ℤ, 0 ≤ z →
      (𝓜 z ≃+ Γ(G ⊗ Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) z, ⊤)))
    (hφ : ∀ (z : ℤ) (hz : 0 ≤ z) (e : ℕ) (hze : 0 ≤ z + e) (a : MvPolynomial (Fin 2) k)
      (ha : a ∈ MvPolynomial.homogeneousSubmodule (Fin 2) k e)
      (y : 𝓜 z) (hay : a • (y : M) ∈ 𝓜 (z + e)),
      φ (z + e) hze ⟨a • (y : M), hay⟩ =
        Scheme.Modules.Hom.app (G ◁ Proj.twistMul z ha) ⊤ (φ z hz y)) :
    ∃ N : ℕ, (Submodule.span (MvPolynomial (Fin 2) k)
      {y : M | ∃ z : ℤ, (N : ℤ) ≤ z ∧ y ∈ 𝓜 z}).FG := by sorry

end AlgebraicGeometry
