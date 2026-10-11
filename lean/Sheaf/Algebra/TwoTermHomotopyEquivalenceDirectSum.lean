/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
import Mathlib.Algebra.DirectSum.Module

/-! # Direct sums of the terms of homotopy equivalent two-term complexes

Source: Stacks Project, Algebra, Lemma 00S3 (lemma-sum-two-terms)
(blueprint: lem-weil-pbc-two-term-homotopy-equivalence-direct-sum).
-/

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
3. Subtracting the off-diagonal term gives inverses for both triangular maps.
   Then `L = U_P⁻¹ ∘ D` is a left inverse for `C`, while `T = D ∘ U_Q⁻¹` is a right inverse.
   The equality `L = L ∘ (C ∘ T) = (L ∘ C) ∘ T = T` gives a common inverse.
   Hence `C` yields the required linear equivalence between the two direct sums.
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
  sorry

end Module
