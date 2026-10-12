/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist
public import WeilConjectures.Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.RingTheory.Finiteness.Defs
import Sheaf.AlgebraicGeometry.Modules.FiniteLocallyFreeTensorExact
import Sheaf.AlgebraicGeometry.ProjShiftedFreeTwist
import Sheaf.AlgebraicGeometry.ProjectiveLineTwistExists
import Sheaf.Paper.PQFCohomology
import Sheaf.RingTheory.GradedSubmoduleFinite
import WeilConjectures.AlgebraicGeometry.Cohomology.ProjectiveLine
import WeilConjectures.AlgebraicGeometry.Cohomology.Serre
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules

/-!
# Finite generation of the graded section module

Source: Stacks Project, Coherent Modules, Lemma 0AG6, part (4)
(blueprint: lem-sc-p1-serre-section-module-finite).

Let `P = Proj k[x₀,x₁]` and `G(n) = G ⊗ 𝒪_P(n)` with `𝒪_P(n) = Proj.twist 𝒜 n`. The
library has no declaration of the graded `S`-module `M_{≥0} = ⨁_{n ≥ 0} Γ(P, G(n))`, so the
statement says that `M_{≥0}` with its canonical action is finitely generated in the landed
form of `coherent_exists_graded_representation`: there is a finitely generated `S`-module `M`,
internally `ℤ`-graded by `𝓜` with `S_e • 𝓜 z ⊆ 𝓜 (e + z)` and `𝓜 z = 0` for `z < 0`, whose
graded pieces `𝓜 z` (`z ≥ 0`) are identified additively with `Γ(P, G(z))` so that
multiplication by a homogeneous `a ∈ S_e` on `M` is the map `G ◁ Proj.twistMul z a` on global
sections. These identifications assemble to an `S`-linear isomorphism `M ≅ M_{≥0}`, so the
existence of `M` is exactly the finite generation of `M_{≥0}` with the induced action.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The truncated graded section module `M_{≥0} = ⨁_{n ≥ 0} Γ(P, G(n))` of a coherent module
`G` on `P = Proj k[x₀,x₁]`, with the action of `S = k[x₀,x₁]` induced by multiplication by
homogeneous polynomials (`G ◁ Proj.twistMul`), is a finitely generated `S`-module: it is
isomorphic, degree by degree and compatibly with homogeneous multiplication, to a finitely
generated graded `S`-module `M` vanishing in negative degrees.

Source: Stacks Project, Coherent Modules, Lemma 0AG6, part (4)
(blueprint: lem-sc-p1-serre-section-module-finite).
Proof: by the twist quotient lemma there is a surjection `⨁ⱼ 𝒪(-mⱼ) ⟶ G` with coherent
kernel `K`; Serre vanishing gives `H¹(P, K(d)) = 0` for `d ≥ d₀`, so
`⨁ⱼ S_{d-mⱼ} = Γ(P, ⨁ⱼ 𝒪(d-mⱼ)) ⟶ Γ(P, G(d))` is surjective for `d ≥ d₀`, and
`⨁_{d ≥ d₀} Γ(P, G(d))` is a quotient of a finite graded submodule of `⨁ⱼ S(-mⱼ)`, hence
finite; the finitely many remaining degrees `0 ≤ d < d₀` are finite-dimensional over `k`
(coherent sheaves on the proper `P` have finite-dimensional global sections). -/
theorem serreSectionModuleFinite (k : Type u) [Field k]
    (G : (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).Modules)
    (hG : RingedSpace.IsCoherent
      (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).toRingedSpace G) :
    ∃ (M : ModuleCat.{u} (MvPolynomial (Fin 2) k)),
      Module.Finite (MvPolynomial (Fin 2) k) M ∧
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
          Scheme.Modules.Hom.app (G ◁ Proj.twistMul z ha) ⊤ (φ z hz y) := by
  sorry

end AlgebraicGeometry
