/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RelativeDifferentialsAffineSectionsMap
import WeilConjectures.AlgebraicGeometry.Modules.Differentials
import WeilConjectures.AlgebraicGeometry.RelativeDifferentialsAffineSectionsMapInjective
import WeilConjectures.AlgebraicGeometry.RelativeDifferentialsAffineSectionsMapSurjective

/-!
# Bijectivity of the affine comparison map for relative differentials

On affine opens, a linear map from the Kähler differentials of the ring map to the sections of
the sheaf of relative differentials that is compatible with the universal derivation is bijective.

## References

* [Stacks Project, Tag 01UT](https://stacks.math.columbia.edu/tag/01UT)
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- A linear map compatible with the universal derivation is the affine comparison
isomorphism, i.e. it is bijective. -/
theorem relativeDifferentials_affine_sections_map_bijective (f : X ⟶ S)
    (U : X.affineOpens) (V : S.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1)
    (e : CommRingCat.KaehlerDifferential (f.appLE V.1 U.1 hUV) →ₗ[Γ(X, U.1)]
      Γ(f.relativeDifferentials, U.1))
    (he : ∀ a : Γ(X, U.1), e (CommRingCat.KaehlerDifferential.d a) =
      f.relativeDifferentialsDerivation.d (X := op U.1) a) :
    Function.Bijective e := by
  exact ⟨relativeDifferentials_affine_sections_map_injective f U V hUV e he,
    relativeDifferentials_affine_sections_map_surjective f U V hUV e he⟩

end AlgebraicGeometry
