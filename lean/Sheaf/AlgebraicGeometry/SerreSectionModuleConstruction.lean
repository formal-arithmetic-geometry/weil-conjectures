/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P3
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist
public import WeilConjectures.Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.DirectSum.Module

/-! # SerreSectionModuleConstruction

Intermediate step for finite generation of graded sections. -/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The nonnegative twisted sections carry their canonical internally graded polynomial action.
No coherence or finiteness is asserted.

Source: Stacks Project, Section 30.14, the graded module in Lemma 01YS(5), and Lemma
0AG6(4); https://stacks.math.columbia.edu/tag/01YS.
(blueprint: lem-sc-p1-section-module-construction).
Proof: take the additive direct sum of the groups Γ(G ⊗ O(n), P), indexed by n ≥ 0.
A homogeneous polynomial a of degree e sends the n-th summand to the (n+e)-th by
G ◁ Proj.twistMul n a. Define the action of an arbitrary polynomial by adding the actions
of its finitely many homogeneous components. Locally, twistMul is multiplication of
fractions, so it is additive in a, sends 1 to the identity, and its composites are
multiplication by the product, after the degree equalities are transported. These facts
prove the module laws. The summand images give the internal integer grading; put zero
in negative degrees. The inverse of each summand inclusion gives φ. Its definition and
the homogeneous action give the asserted compatibility, including degree zero. -/
theorem serreSectionModuleConstruction
    (k : Type u) [Field k]
    (G : (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).Modules)
 :
    ∃ (M : ModuleCat.{u} (MvPolynomial (Fin 2) k)),
    ∃ (𝓜 : ℤ → AddSubgroup M), DirectSum.IsInternal 𝓜 ∧
      (∀ (e : ℕ) (z : ℤ) (a : MvPolynomial (Fin 2) k) (y : M),
        a ∈ MvPolynomial.homogeneousSubmodule (Fin 2) k e → y ∈ 𝓜 z → a • y ∈ 𝓜 (e + z)) ∧
      (∀ z : ℤ, z < 0 → 𝓜 z = ⊥) ∧
    ∃ (φ : ∀ z : ℤ, 0 ≤ z →
        (𝓜 z ≃+ Γ(G ⊗ Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) z, ⊤))),
      ∀ (z : ℤ) (hz : 0 ≤ z) (e : ℕ) (hze : 0 ≤ z + e) (a : MvPolynomial (Fin 2) k)
        (ha : a ∈ MvPolynomial.homogeneousSubmodule (Fin 2) k e)
        (y : 𝓜 z) (hay : a • (y : M) ∈ 𝓜 (z + e)),
        φ (z + e) hze ⟨a • (y : M), hay⟩ =
          Scheme.Modules.Hom.app (G ◁ Proj.twistMul z ha) ⊤ (φ z hz y) := by sorry

end AlgebraicGeometry
