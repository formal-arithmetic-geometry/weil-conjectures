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

import Sheaf.AlgebraicGeometry.SerreSectionModuleComponentFinite
import Sheaf.AlgebraicGeometry.SerreSectionCoordinateSurjective

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
Proof: eventual coordinate surjectivity gives N such that every section of G(z+1)
for z ≥ N is x₀ times a section of G(z) plus x₁ times another section. Pull both
sections back through φ(z), use hsmul for their subtype membership, and apply hφ
and injectivity of φ(z+1) to obtain the same coordinate decomposition in M.
Let L be the polynomial span of the degree-N subgroup. Component finiteness makes
L finitely generated. Induction starting at N, using the coordinate decomposition
and closure of L under addition and scalar multiplication, puts every nonnegative
degree at least N in L. An integer degree at least N is nonnegative, hence equals
its natural-number conversion. Thus the span of the tail is contained in L.
Conversely degree N belongs to the tail, giving the reverse inclusion. The two
spans are equal, and component finiteness proves the conclusion. -/
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
      {y : M | ∃ z : ℤ, (N : ℤ) ≤ z ∧ y ∈ 𝓜 z}).FG := by
  classical
  obtain ⟨N, hN⟩ := serreSectionCoordinateSurjective k G hG
  let L := Submodule.span (MvPolynomial (Fin 2) k) (𝓜 (N : ℤ) : Set M)
  have hL : L.FG := serreSectionModuleComponentFinite k G hG M 𝓜 hsmul φ hφ N
  have hstep (z : ℤ) (hz : (N : ℤ) ≤ z) (y : 𝓜 (z + (1 : ℕ))) :
      ∃ y₀ y₁ : 𝓜 z, (y : M) =
        (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) k) • (y₀ : M) +
        (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) k) • (y₁ : M) := by
    have hz0 : 0 ≤ z := le_trans (Int.natCast_nonneg N) hz
    have hz1 : 0 ≤ z + (1 : ℕ) := by omega
    obtain ⟨s₀, s₁, hs⟩ := hN z hz (φ (z + (1 : ℕ)) hz1 y)
    let y₀ := (φ z hz0).symm s₀
    let y₁ := (φ z hz0).symm s₁
    have hx₀ := MvPolynomial.X_mem_homogeneousSubmodule_one k (0 : Fin 2)
    have hx₁ := MvPolynomial.X_mem_homogeneousSubmodule_one k (1 : Fin 2)
    have hy₀ : (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) k) • (y₀ : M) ∈
        𝓜 (z + (1 : ℕ)) := by
      simpa only [add_comm] using hsmul 1 z _ y₀ hx₀ y₀.property
    have hy₁ : (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) k) • (y₁ : M) ∈
        𝓜 (z + (1 : ℕ)) := by
      simpa only [add_comm] using hsmul 1 z _ y₁ hx₁ y₁.property
    refine ⟨y₀, y₁, ?_⟩
    have he : y =
        ⟨(MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) k) • (y₀ : M), hy₀⟩ +
        ⟨(MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) k) • (y₁ : M), hy₁⟩ := by
      apply (φ (z + (1 : ℕ)) hz1).injective
      have hp₀ := hφ z hz0 1 hz1 _ hx₀ y₀ hy₀
      have hp₁ := hφ z hz0 1 hz1 _ hx₁ y₁ hy₁
      rw [map_add, hp₀, hp₁]
      simpa only [y₀, y₁, AddEquiv.apply_symm_apply] using hs
    exact congrArg Subtype.val he
  have hdegree : ∀ (n : ℕ), N ≤ n → ∀ y : M, y ∈ 𝓜 (n : ℤ) → y ∈ L := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      intro y hy
      exact Submodule.subset_span hy
    | succ n hn ih =>
      intro y hy
      have hy' : y ∈ 𝓜 ((n : ℤ) + 1) := by simpa using hy
      obtain ⟨y₀, y₁, he⟩ := hstep (n : ℤ) (by exact_mod_cast hn) ⟨y, hy'⟩
      change y = _ at he
      rw [he]
      exact L.add_mem (L.smul_mem _ (ih y₀ y₀.property))
        (L.smul_mem _ (ih y₁ y₁.property))
  refine ⟨N, ?_⟩
  have heq : Submodule.span (MvPolynomial (Fin 2) k)
      {y : M | ∃ z : ℤ, (N : ℤ) ≤ z ∧ y ∈ 𝓜 z} = L := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro y ⟨z, hz, hy⟩
      have hz0 : 0 ≤ z := le_trans (Int.natCast_nonneg N) hz
      have hzn : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hz0
      apply hdegree z.toNat (by omega) y
      simpa only [hzn] using hy
    · apply Submodule.span_le.mpr
      intro y hy
      exact Submodule.subset_span ⟨(N : ℤ), le_rfl, hy⟩
  rw [heq]
  exact hL

end AlgebraicGeometry
