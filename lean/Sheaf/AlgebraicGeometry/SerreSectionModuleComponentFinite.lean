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

import Sheaf.AlgebraicGeometry.ProjShiftedFreeTwist
import Sheaf.AlgebraicGeometry.ProjectiveLineTwistExists
import WeilConjectures.AlgebraicGeometry.Cohomology.ProjectiveLine
import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules

/-! # SerreSectionModuleComponentFinite

Intermediate step for finite generation of graded sections. -/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Each individual nonnegative section degree generates a finite polynomial submodule.
This is a statement for one degree at a time, and supplies no uniform bound on degrees.

Source: Stacks Project, Lemma 01YS(3) and the last paragraph of the proof of (5);
https://stacks.math.columbia.edu/tag/01YS.
(blueprint: lem-sc-p1-section-module-component-finite).
Proof: O(n) is invertible, so G ⊗ O(n) is coherent by local triviality. Transport to the
standard projective line via the Proj chart isomorphism and the twist identification.
Coherent global sections are finite-dimensional over k by finiteDimensional_H in degree
zero and the identification of H⁰ with Γ. Degree-zero multiplication in hφ, applied to
constant polynomials C(c), makes φ(n) k-linear for the restricted scalar action on the
n-th subgroup: twistMul by C(c) is multiplication by c on the local fractions. Pull back
a finite k-basis of sections. Every element of the subgroup is a k-linear combination
of this finite set, hence belongs to its S-span. Conversely the set is in the subgroup,
so its S-span equals the S-span of the entire subgroup. This gives FG. In the zero
section space the empty basis suffices; n=0 uses the same argument. -/
theorem serreSectionModuleComponentFinite
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
    ∀ n : ℕ, (Submodule.span (MvPolynomial (Fin 2) k) (𝓜 (n : ℤ) : Set M)).FG := by sorry

end AlgebraicGeometry
