/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.PolynomialAffineSpace

/-!
# Smoothness of the affine space `𝔸ᴺ_k`

The affine space `𝔸ᴺ_k = Spec k[X₀, …, X_{N-1}]` (`AlgebraicGeometry.polyAffine`) is smooth of
relative dimension `N` over `k` (`AlgebraicGeometry.smoothOfRelativeDimension_polyAffine_hom`), in
particular smooth (`AlgebraicGeometry.smooth_polyAffine_hom`).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k]

/-- The affine space `𝔸ᴺ_k` is smooth of relative dimension `N` over `k`. -/
instance smoothOfRelativeDimension_polyAffine_hom (N : ℕ) :
    SmoothOfRelativeDimension N (polyAffine k N).hom := by
  change SmoothOfRelativeDimension N
    (Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin N) k))))
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension N), CommRingCat.hom_ofHom]
  exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
    ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap N).2
      (isStandardSmoothOfRelativeDimension_mvPolynomial k N))

/-- The affine space `𝔸ᴺ_k` is smooth over `k`. -/
instance smooth_polyAffine_hom (N : ℕ) : Smooth (polyAffine k N).hom :=
  SmoothOfRelativeDimension.smooth N _

end AlgebraicGeometry
