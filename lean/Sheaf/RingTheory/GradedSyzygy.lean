/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Sheaf.Algebra.Category.ModuleCat.TorSymmetry
import Sheaf.Algebra.TorDimensionShifting
import Sheaf.AlgebraicGeometry.ProjectiveSpace.KoszulResolution
import Sheaf.RingTheory.FiniteHomogeneousGenerators
import Sheaf.RingTheory.GradedKernelFinite
import Sheaf.RingTheory.GradedNakayamaFree

/-!
# Graded syzygies over the two-variable polynomial ring

Source: Weil conjectures blueprint, `sec-picard-framework/sk-thm-picard-duality`,
`lem-sc-p1-graded-resolution`, proof, first sentence (blueprint: lem-sc-p1-graded-syzygy).
-/

@[expose] public section

universe u v

namespace MvPolynomial

/-- A finite graded module over `k[x₀,x₁]` has a finite graded free resolution of length two.
Source: blueprint `lem-sc-p1-graded-resolution`, proof, first sentence
(blueprint: lem-sc-p1-graded-syzygy).

`homogeneousSubmodule` is the total-degree grading, extended by zero in negative degrees.
A finite homogeneous basis of degrees `-d a` presents a finite sum of shifts `S(d a)`:
the convention of `def-weil-pbc-proj-twisting-sheaf` (2) is `S(d)_n = S_{d+n}`.
The index `i : Fin 3` labels `F₀,F₁,F₂`; ranks may be zero and shifts may be any integer.
The sheaf conventions of `def-sc-p1-standard` do not enter this module statement.

Proof:
1. By `lem-sc-p1-finite-homogeneous-generators`, choose finite homogeneous generators of `M`.
   They give a surjective degree-zero map from a finite sum `F₀` of shifts of `S`.
2. Its kernel `K₁` is graded and finite by `lem-sc-p1-graded-kernel-finite`. Apply
   `lem-sc-p1-finite-homogeneous-generators` again to obtain `F₁ → K₁` and hence `F₁ → F₀`.
3. The second kernel `K₂` is graded and finite by `lem-sc-p1-graded-kernel-finite`.
   The length-two Koszul resolution of `k` (`lem-sc-p1-koszul-resolution`), Tor symmetry
   (`lem-weil-pbc-tor-symmetry`), and the definition `def-weil-pbc-tor-modules` give
   `Tor₃(M,k) = 0`. Then `lem-sc-p1-tor-dimension-shifting` gives `Tor₁(K₂,k) = 0`.
4. By `lem-sc-p1-graded-nakayama-free`, `K₂` is a finite sum of shifts. Take `F₂ = K₂`
   with its inclusion into `F₁`. The kernel identifications give exactness at both middle
   terms; the inclusion is injective and the augmentation is surjective. -/
theorem exists_graded_free_resolution_two {k : Type u} [Field k]
    {M : Type v} [AddCommGroup M] [Module (MvPolynomial (Fin 2) k) M]
    [Module.Finite (MvPolynomial (Fin 2) k) M]
    (ℳ : ℤ → AddSubgroup M) (hℳ : DirectSum.IsInternal ℳ)
    (hsmul : ∀ (n : ℕ) (j : ℤ) (s : MvPolynomial (Fin 2) k) (x : M),
      s ∈ homogeneousSubmodule (Fin 2) k n → x ∈ ℳ j → s • x ∈ ℳ ((n : ℤ) + j)) :
    ∃ (F : Fin 3 → ModuleCat.{u} (MvPolynomial (Fin 2) k))
      (𝒢 : ∀ i : Fin 3, ℤ → AddSubgroup (F i)) (r : Fin 3 → ℕ)
      (d : ∀ i : Fin 3, Fin (r i) → ℤ)
      (b : ∀ i : Fin 3, Module.Basis (Fin (r i)) (MvPolynomial (Fin 2) k) (F i))
      (f₂ : F 2 →ₗ[MvPolynomial (Fin 2) k] F 1)
      (f₁ : F 1 →ₗ[MvPolynomial (Fin 2) k] F 0)
      (f₀ : F 0 →ₗ[MvPolynomial (Fin 2) k] M),
      (∀ i : Fin 3, DirectSum.IsInternal (𝒢 i)) ∧
      (∀ (i : Fin 3) (n : ℕ) (j : ℤ) (s : MvPolynomial (Fin 2) k) (x : F i),
        s ∈ homogeneousSubmodule (Fin 2) k n → x ∈ 𝒢 i j →
          s • x ∈ 𝒢 i ((n : ℤ) + j)) ∧
      (∀ (i : Fin 3) (a : Fin (r i)), b i a ∈ 𝒢 i (-(d i a))) ∧
      (∀ (j : ℤ) (x : F 2), x ∈ 𝒢 2 j → f₂ x ∈ 𝒢 1 j) ∧
      (∀ (j : ℤ) (x : F 1), x ∈ 𝒢 1 j → f₁ x ∈ 𝒢 0 j) ∧
      (∀ (j : ℤ) (x : F 0), x ∈ 𝒢 0 j → f₀ x ∈ ℳ j) ∧
      Function.Injective f₂ ∧ LinearMap.range f₂ = LinearMap.ker f₁ ∧
      LinearMap.range f₁ = LinearMap.ker f₀ ∧ Function.Surjective f₀ := by
  sorry

end MvPolynomial
