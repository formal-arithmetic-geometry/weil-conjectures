/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.PolynomialAffineSpace

/-!
# Smoothness of the affine space `𝔸ᴺ_k`

The affine space `𝔸ᴺ_k = Spec k[X₀, …, X_{N-1}]` (`AlgebraicGeometry.polyAffine`) is smooth over
`k`: it is an iterated affine line, `𝔸^{N+1}_k ⟶ 𝔸ᴺ_k` being smooth of relative dimension `1`.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k]

/-- The affine space `𝔸ᴺ_k` is smooth over `k`. -/
instance smooth_polyAffine_hom (N : ℕ) : Smooth (polyAffine k N).hom := by
  induction N with
  | zero => infer_instance
  | succ N ih =>
    have := SmoothOfRelativeDimension.smooth 1 (polyAffineProj k N).left
    rw [← CategoryTheory.Over.w (polyAffineProj k N)]
    infer_instance

end AlgebraicGeometry
