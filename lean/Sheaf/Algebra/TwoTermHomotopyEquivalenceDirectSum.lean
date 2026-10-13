/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Mathlib.Algebra.DirectSum.Module

import Mathlib.Tactic.Abel

/-! # Direct sums of the terms of homotopy equivalent two-term complexes

Source: Stacks Project, Algebra, Lemma 00S3 (lemma-sum-two-terms)
(blueprint: lem-weil-pbc-two-term-homotopy-equivalence-direct-sum).
-/

@[expose] public section

universe u v₁ v₀ w₁ w₀

namespace Module

/-- Homotopy equivalent two-term complexes have isomorphic crosswise binary direct sums.
The binary direct sum of modules is represented by the product with componentwise operations;
this is the finite two-summand case of `DirectSum` (def-weil-pbc-direct-sum-modules).

Source: Stacks Project, Algebra, Lemma 00S3 (lemma-sum-two-terms)
(blueprint: lem-weil-pbc-two-term-homotopy-equivalence-direct-sum).

Proof plan:
1. Set `P = A₁ × B₀` and `Q = B₁ × A₀`, the binary direct sums from
   def-weil-pbc-direct-sum-modules. Define linear maps
   `C(a,b) = (φ₁(a) - h'(b), dA(a) + ψ₀(b))` and
   `D(c,e) = (ψ₁(c) + h(e), -dB(c) + φ₀(e))`.
2. Expand both compositions using the two chain-map equations and the four homotopy equations.
   The first component of `DC(a,b)` is `a + (h ∘ ψ₀ - ψ₁ ∘ h')(b)` and its second is `b`.
   The first component of `CD(c,e)` is `c + (φ₁ ∘ h - h' ∘ φ₀)(e)` and its second is `e`.
   Thus `DC = U_P` and `CD = U_Q` are upper triangular maps with identity diagonal.
3. Equality of two images under `C` gives equality under `DC`. Comparing second
   coordinates, then cancelling the equal off-diagonal terms in the first coordinates,
   proves injectivity. For `(c,e)` in `Q`, apply `D` to `(c-v(e),e)`; the formula for
   `CD` shows its image under `C` is `(c,e)`, proving surjectivity.
   Use `LinearEquiv.ofBijective` to obtain the required linear equivalence.
-/
theorem prod_linearEquiv_of_twoTermHomotopy
    (R : Type u) [CommRing R]
    (A₁ : Type v₁) (A₀ : Type v₀) (B₁ : Type w₁) (B₀ : Type w₀)
    [AddCommGroup A₁] [AddCommGroup A₀] [AddCommGroup B₁] [AddCommGroup B₀]
    [Module R A₁] [Module R A₀] [Module R B₁] [Module R B₀]
    (dA : A₁ →ₗ[R] A₀) (dB : B₁ →ₗ[R] B₀)
    (φ₁ : A₁ →ₗ[R] B₁) (φ₀ : A₀ →ₗ[R] B₀)
    (ψ₁ : B₁ →ₗ[R] A₁) (ψ₀ : B₀ →ₗ[R] A₀)
    (hφ : dB.comp φ₁ = φ₀.comp dA)
    (hψ : dA.comp ψ₁ = ψ₀.comp dB)
    (h : A₀ →ₗ[R] A₁) (h' : B₀ →ₗ[R] B₁)
    (hA₁ : LinearMap.id - ψ₁.comp φ₁ = h.comp dA)
    (hA₀ : LinearMap.id - ψ₀.comp φ₀ = dA.comp h)
    (hB₁ : LinearMap.id - φ₁.comp ψ₁ = h'.comp dB)
    (hB₀ : LinearMap.id - φ₀.comp ψ₀ = dB.comp h') :
    Nonempty ((A₁ × B₀) ≃ₗ[R] (B₁ × A₀)) := by
  let C : (A₁ × B₀) →ₗ[R] (B₁ × A₀) :=
    (φ₁.coprod (-h')).prod (dA.coprod ψ₀)
  let D : (B₁ × A₀) →ₗ[R] (A₁ × B₀) :=
    (ψ₁.coprod h).prod ((-dB).coprod φ₀)
  have hφ_apply (a : A₁) : dB (φ₁ a) = φ₀ (dA a) :=
    DFunLike.congr_fun hφ a
  have hψ_apply (b : B₁) : dA (ψ₁ b) = ψ₀ (dB b) :=
    DFunLike.congr_fun hψ b
  have hA₁_apply (a : A₁) : a - ψ₁ (φ₁ a) = h (dA a) :=
    DFunLike.congr_fun hA₁ a
  have hA₀_apply (a : A₀) : a - ψ₀ (φ₀ a) = dA (h a) :=
    DFunLike.congr_fun hA₀ a
  have hB₁_apply (b : B₁) : b - φ₁ (ψ₁ b) = h' (dB b) :=
    DFunLike.congr_fun hB₁ b
  have hB₀_apply (b : B₀) : b - φ₀ (ψ₀ b) = dB (h' b) :=
    DFunLike.congr_fun hB₀ b
  have hDC (x : A₁ × B₀) :
      D (C x) = (x.1 + (h (ψ₀ x.2) - ψ₁ (h' x.2)), x.2) := by
    ext
    · change ψ₁ (φ₁ x.1 + -(h' x.2)) + h (dA x.1 + ψ₀ x.2) = _
      simp only [map_add, map_neg]
      rw [← hA₁_apply]
      abel
    · change -dB (φ₁ x.1 + -(h' x.2)) + φ₀ (dA x.1 + ψ₀ x.2) = _
      simp only [map_add, map_neg]
      rw [hφ_apply, ← hB₀_apply]
      abel
  have hCD (y : B₁ × A₀) :
      C (D y) = (y.1 + (φ₁ (h y.2) - h' (φ₀ y.2)), y.2) := by
    ext
    · change φ₁ (ψ₁ y.1 + h y.2) + -(h' (-dB y.1 + φ₀ y.2)) = _
      simp only [map_add, map_neg]
      rw [← hB₁_apply]
      abel
    · change dA (ψ₁ y.1 + h y.2) + ψ₀ (-dB y.1 + φ₀ y.2) = _
      simp only [map_add, map_neg]
      rw [hψ_apply, ← hA₀_apply]
      abel
  have hinj : Function.Injective C := by
    intro x y hxy
    have hd : D (C x) = D (C y) := congrArg D hxy
    rw [hDC, hDC] at hd
    have hs := congrArg (fun p : A₁ × B₀ => p.2) hd
    change x.2 = y.2 at hs
    have hf := congrArg (fun p : A₁ × B₀ => p.1) hd
    simp only at hf
    rw [hs] at hf
    exact Prod.ext (add_right_cancel hf) hs
  have hsurj : Function.Surjective C := by
    intro y
    refine ⟨D (y.1 - (φ₁ (h y.2) - h' (φ₀ y.2)), y.2), ?_⟩
    rw [hCD]
    simp
  exact ⟨LinearEquiv.ofBijective C ⟨hinj, hsurj⟩⟩

end Module
