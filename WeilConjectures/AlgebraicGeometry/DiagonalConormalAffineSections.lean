/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DiagonalConormalDerivation
import WeilConjectures.AlgebraicGeometry.DiagonalConormalAffineSectionsBase
import WeilConjectures.AlgebraicGeometry.DiagonalConormalAffineSectionsUnique

/-!
# Normalized diagonal conormal sections on an affine chart

## References

* Stacks Project, Tags 01KJ, 01R3, 08S2 and 00RW
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- The diagonal conormal on an affine chart is the ring's Kähler differential module.
Every normalized difference derivation has the expected formula in these coordinates
(Stacks, Tags 08S2, 01KJ, 01R3 and 00RW). -/
theorem diagonalConormal_affine_sections (f : X ⟶ S)
    (U : X.affineOpens) (V : S.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1) :
    ∃ e : CommRingCat.KaehlerDifferential (f.appLE V.1 U.1 hUV) ≃ₗ[Γ(X, U.1)]
        Γ(diagonalConormal f, U.1),
      ∀ (D : (diagonalConormal f).val.Derivation' f.pullbackPresheafToPresheaf),
        IsDiagonalConormalDerivation f D → ∀ a : Γ(X, U.1),
          e (CommRingCat.KaehlerDifferential.d a) = D.d (X := op U.1) a := by
  obtain ⟨D₀, hD₀⟩ := exists_diagonalConormalDerivation f
  obtain ⟨e, he⟩ := exists_diagonalConormal_affine_sections_base f U V hUV D₀ hD₀
  refine ⟨e, ?_⟩
  intro D hD a
  rw [he]
  exact (diagonalConormal_affine_sections_unique f U.1 D₀ D hD₀ hD a)

end AlgebraicGeometry
