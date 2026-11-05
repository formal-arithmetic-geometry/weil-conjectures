/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology
public import Mathlib.RingTheory.GradedAlgebra.Radical
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Finiteness.Subalgebra
public import WeilConjectures.Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-!
# Standard graded algebras

Let `k` be a field. A *standard graded `k`-algebra* is an `ℕ`-graded commutative `k`-algebra
`S = ⨁ₙ Sₙ` which is generated as a `k`-algebra by finitely many elements of degree one. Then
`S₀ = k` (more precisely, `S₀` is the image of `k`), and every `Sₙ = S₁ ^ n` is a
finite-dimensional `k`-vector space.

Given two linear forms `l₀, l₁ ∈ S₁` without common zero on `Proj S`, we show that
`S_{n + 1} = l₀ Sₙ + l₁ Sₙ` for all large `n`, that `S` is a finite module over the subalgebra
`k[l₀, l₁]`, and that the degree-zero part `S_(l₀)` of `S[l₀⁻¹]` is a finite module over the
subalgebra `k[l₁ / l₀]`. Geometrically, the last statement is the algebraic content of the
finiteness of the morphism `Proj S → ℙ¹` given by `[l₀ : l₁]` over the chart `D₊(l₀)`.

## Main definitions

- `GradedAlgebra.IsStandard 𝒜` — the grading `𝒜` makes `S` a standard graded `k`-algebra.

## Main statements

- `GradedAlgebra.IsStandard.grade_eq_pow` — `𝒜 n = 𝒜 1 ^ n`.
- `GradedAlgebra.IsStandard.grade_zero_eq_one` — `𝒜 0 = 1`, i.e. `S₀` is the image of `k`.
- `GradedAlgebra.IsStandard.finite_grade` — each `𝒜 n` is finite-dimensional over `k`.
- `GradedAlgebra.IsStandard.exists_grade_succ_eq_span_mul` — if `l₀, l₁ ∈ S₁` have no common
  zero on `Proj S`, then `S_{n + 1} = (k l₀ + k l₁) Sₙ` for all large `n`.
- `GradedAlgebra.IsStandard.finite_adjoin_pair` — then `S` is finite over `k[l₀, l₁]`.
- `GradedAlgebra.IsStandard.finite_away` — and `S_(l₀)` is finite over `k[l₁ / l₀]`.

The statement that a vector space over an infinite field is not a finite union of proper
subspaces (blueprint `lem-pc-finite-linear-avoidance`) is `Subspace.iUnion_ne_univ_of_ne_top`,
a restatement of Mathlib's `Subspace.biUnion_ne_univ_of_top_notMem`.
-/

@[expose] public section

namespace HomogeneousLocalization.Away

variable {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [AddCommMonoid ι]
  [DecidableEq ι] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] {d : ι} {f : A}

end HomogeneousLocalization.Away

namespace GradedAlgebra

variable {k S : Type*} [Field k] [CommRing S] [Algebra k S] (𝒜 : ℕ → Submodule k S)
  [GradedAlgebra 𝒜]

namespace IsStandard

variable {𝒜} [IsStandard 𝒜]

open ProjectiveSpectrum

open HomogeneousLocalization

end IsStandard

end GradedAlgebra
