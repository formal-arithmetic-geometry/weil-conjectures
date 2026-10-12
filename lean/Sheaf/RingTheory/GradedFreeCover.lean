/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Sheaf.RingTheory.FiniteHomogeneousGenerators

/-!
# Finite graded free covers

Source: blueprint `lem-sc-p1-graded-resolution`, construction of the first free module.
-/

@[expose] public section

universe u v

namespace MvPolynomial

/-- A finite graded module admits a surjection from a finite free module with homogeneous basis.
Source: blueprint `lem-sc-p1-graded-resolution`, proof, choose homogeneous generators
(blueprint: lem-sc-p1-graded-free-cover).

Proof: apply `exists_finite_homogeneous_generators` to obtain generators `m a` of degrees
`e a` and its surjective map from `Fin r →₀ S`, where `S = k[x₀,x₁]`. Give this free module
its shifted grading: a vector belongs to degree `j` if its coefficient at `a` belongs to the
polynomial homogeneous part of degree `j - e a`, with that part zero for negative degrees.
Decompose each coefficient into total-degree homogeneous polynomials and collect terms of
common shifted degree. Each vector has only finitely many such terms, and uniqueness follows
coefficientwise from uniqueness of the polynomial decomposition. This proves internality.
Multiplication by a homogeneous polynomial of degree `n` raises each shifted coefficient degree
by `n`, proving scalar compatibility. The standard basis vector at `a` has degree `e a`.
Linearity and the degree assertion of the generator theorem show that the map preserves each
homogeneous part. Take the shift parameter `d a = -e a`. This includes the empty basis when
`M = 0`. The source has universe `u` independently of the target's universe `v`. -/
theorem exists_graded_free_cover {k : Type u} [Field k]
    {M : Type v} [AddCommGroup M] [Module (MvPolynomial (Fin 2) k) M]
    [Module.Finite (MvPolynomial (Fin 2) k) M]
    (ℳ : ℤ → AddSubgroup M) (hℳ : DirectSum.IsInternal ℳ)
    (hsmul : ∀ (n : ℕ) (j : ℤ) (s : MvPolynomial (Fin 2) k) (x : M),
      s ∈ homogeneousSubmodule (Fin 2) k n → x ∈ ℳ j → s • x ∈ ℳ ((n : ℤ) + j)) :
    ∃ (F : ModuleCat.{u} (MvPolynomial (Fin 2) k))
      (𝒢 : ℤ → AddSubgroup F) (r : ℕ) (d : Fin r → ℤ)
      (b : Module.Basis (Fin r) (MvPolynomial (Fin 2) k) F)
      (q : F →ₗ[MvPolynomial (Fin 2) k] M),
      DirectSum.IsInternal 𝒢 ∧
      (∀ (n : ℕ) (j : ℤ) (s : MvPolynomial (Fin 2) k) (x : F),
        s ∈ homogeneousSubmodule (Fin 2) k n → x ∈ 𝒢 j → s • x ∈ 𝒢 ((n : ℤ) + j)) ∧
      (∀ a : Fin r, b a ∈ 𝒢 (-(d a))) ∧
      (∀ (j : ℤ) (x : F), x ∈ 𝒢 j → q x ∈ ℳ j) ∧ Function.Surjective q := by sorry

end MvPolynomial
