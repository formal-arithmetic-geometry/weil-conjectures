/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Module.Projective

/-! # Schanuel's lemma

Source: literature/stacks-project/algebra.tex, Algebra, Lemma Tag 00O3
(blueprint: lem-weil-pbc-schanuel)
-/

@[expose] public section

namespace Module

universe u v₁ v₂ v₃ v₄ v₅

/-- Schanuel's lemma for two projective presentations.

Source: literature/stacks-project/algebra.tex, Algebra, Lemma Tag 00O3
(blueprint: lem-weil-pbc-schanuel).

Proof:
1. Form `N = {(u, v) ∈ P₁ ⊕ P₂ | p₁(u) + p₂(v) = 0}`. Its coordinate
   projections `q₁ : N → P₁` and `q₂ : N → P₂` are surjective: lift `-p₁(u)`
   along `p₂`, respectively `-p₂(v)` along `p₁`. Exactness
   (def-weil-pbc-exact-sequence) identifies `ker q₁` with `L` via
   `l ↦ (0, c₂(l))` and `ker q₂` with `K` via `k ↦ (c₁(k), 0)`.
   This gives short exact sequences `0 → L → N → P₁ → 0` and
   `0 → K → N → P₂ → 0`.
2. Projectivity (def-weil-pbc-projective-module) and
   lem-weil-pbc-ses-projective-quotient-splits give linear sections
   `s₁ : P₁ → N` and `s₂ : P₂ → N` with `q₁ ∘ s₁ = id` and `q₂ ∘ s₂ = id`.
3. The map `(l, u) ↦ (0, c₂(l)) + s₁(u)` identifies `L ⊕ P₁` with `N`.
   Its inverse sends `n` to `(l, q₁(n))`, where exactness uniquely determines
   `l` from `n - s₁(q₁(n)) = (0, c₂(l))`. Similarly
   `(k, v) ↦ (c₁(k), 0) + s₂(v)` identifies `K ⊕ P₂` with `N`; its inverse
   uses `n - s₂(q₂(n)) ∈ ker q₂`. Compose the second isomorphism with the
   inverse of the first to obtain `K ⊕ P₂ ≅ L ⊕ P₁`.
-/
theorem schanuel (R : Type u) [CommRing R]
    (K : Type v₁) (L : Type v₂) (P₁ : Type v₃) (P₂ : Type v₄) (M : Type v₅)
    [AddCommGroup K] [AddCommGroup L] [AddCommGroup P₁]
    [AddCommGroup P₂] [AddCommGroup M]
    [Module R K] [Module R L] [Module R P₁] [Module R P₂] [Module R M]
    (c₁ : K →ₗ[R] P₁) (p₁ : P₁ →ₗ[R] M)
    (c₂ : L →ₗ[R] P₂) (p₂ : P₂ →ₗ[R] M)
    (hc₁ : Function.Injective c₁) (h₁ : Function.Exact c₁ p₁)
    (hp₁ : Function.Surjective p₁)
    (hc₂ : Function.Injective c₂) (h₂ : Function.Exact c₂ p₂)
    (hp₂ : Function.Surjective p₂)
    [Module.Projective R P₁] [Module.Projective R P₂] :
    Nonempty ((K × P₂) ≃ₗ[R] (L × P₁)) := by
  sorry

end Module
