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

import Sheaf.AlgebraicGeometry.SerreSectionModuleConstruction
import Sheaf.AlgebraicGeometry.SerreSectionModuleTailFinite
import Sheaf.AlgebraicGeometry.SerreSectionModuleComponentFinite
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Algebra.DirectSum.Decomposition

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
  classical
  obtain ⟨M, 𝓜, h𝓜, hsmul, hneg, φ, hφ⟩ := serreSectionModuleConstruction k G
  obtain ⟨N, htail⟩ := serreSectionModuleTailFinite k G hG M 𝓜 hsmul φ hφ
  have hpiece := serreSectionModuleComponentFinite k G hG M 𝓜 hsmul φ hφ
  let T := Submodule.span (MvPolynomial (Fin 2) k)
    {y : M | ∃ z : ℤ, (N : ℤ) ≤ z ∧ y ∈ 𝓜 z}
  let L := ⨆ i : Fin N,
    Submodule.span (MvPolynomial (Fin 2) k) (𝓜 (i : ℤ) : Set M)
  have hL : L.FG := Submodule.fg_iSup _ (fun i ↦ hpiece i)
  have htop : T ⊔ L = ⊤ := by
    let : DirectSum.Decomposition 𝓜 := h𝓜.chooseDecomposition
    apply Submodule.eq_top_iff'.mpr
    refine DirectSum.Decomposition.inductionOn 𝓜
      (motive := fun x ↦ x ∈ T ⊔ L) ?_ ?_ ?_
    · exact Submodule.zero_mem _
    · intro z y
      by_cases hz : z < 0
      · have hy : (y : M) = 0 := by
          exact (hneg z hz).le y.property
        rw [hy]
        exact Submodule.zero_mem _
      · by_cases hNz : (N : ℤ) ≤ z
        · exact Submodule.mem_sup_left (Submodule.subset_span ⟨z, hNz, y.property⟩)
        · have hzn : (z.toNat : ℤ) = z := Int.toNat_of_nonneg (by omega)
          have hi : z.toNat < N := by omega
          apply Submodule.mem_sup_right
          apply (le_iSup (fun i : Fin N ↦
            Submodule.span (MvPolynomial (Fin 2) k) (𝓜 (i : ℤ) : Set M))
            ⟨z.toNat, hi⟩)
          apply Submodule.subset_span
          change (y : M) ∈ 𝓜 (z.toNat : ℤ)
          rw [hzn]
          exact y.property
    · intro x y hx hy
      exact Submodule.add_mem _ hx hy
  have hfinite : Module.Finite (MvPolynomial (Fin 2) k) M := by
    apply Module.Finite.of_fg_top
    rw [← htop]
    exact htail.sup hL
  exact ⟨M, hfinite, 𝓜, h𝓜, hsmul, hneg, φ, hφ⟩

end AlgebraicGeometry
