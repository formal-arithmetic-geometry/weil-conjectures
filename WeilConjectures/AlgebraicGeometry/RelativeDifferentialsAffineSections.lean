/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
import WeilConjectures.AlgebraicGeometry.RelativeDifferentialsAffineSectionsMap
import WeilConjectures.AlgebraicGeometry.RelativeDifferentialsAffineSectionsMapBijective

/-!
# Differential sections on an affine chart

## References

* [Stacks Project, Tag 01UT](https://stacks.math.columbia.edu/tag/01UT)
* [Stacks Project, Tag 08S2](https://stacks.math.columbia.edu/tag/08S2)
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- On an affine chart, differential sections are the ring's Kähler differentials,
compatibly with the universal derivation. -/
theorem relativeDifferentials_affine_sections (f : X ⟶ S)
    (U : X.affineOpens) (V : S.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1) :
    ∃ e : CommRingCat.KaehlerDifferential (f.appLE V.1 U.1 hUV) ≃ₗ[Γ(X, U.1)]
        Γ(f.relativeDifferentials, U.1),
      ∀ a : Γ(X, U.1), e (CommRingCat.KaehlerDifferential.d a) =
        f.relativeDifferentialsDerivation.d (X := op U.1) a := by
  obtain ⟨e, he⟩ := relativeDifferentials_affine_sections_map f U V hUV
  exact ⟨LinearEquiv.ofBijective e
    (relativeDifferentials_affine_sections_map_bijective f U V hUV e he), he⟩

end AlgebraicGeometry
