module

public import Sheaf.AlgebraicGeometry.RelativeDifferentialsAffineSectionsMap
import WeilConjectures.AlgebraicGeometry.Modules.Differentials

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- A linear map compatible with the universal derivation is the affine comparison
isomorphism.  This is the injectivity and surjectivity part of the affine calculation.
Source: Stacks Project, Tag 01UT; affine comparison and the universal property.
(blueprint: lem-sc-relative-differentials-affine-sections-map-bijective).
-/
theorem relativeDifferentials_affine_sections_map_bijective (f : X ⟶ S)
    (U : X.affineOpens) (V : S.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1)
    (e : CommRingCat.KaehlerDifferential (f.appLE V.1 U.1 hUV) →ₗ[Γ(X, U.1)]
      Γ(f.relativeDifferentials, U.1))
    (he : ∀ a : Γ(X, U.1), e (CommRingCat.KaehlerDifferential.d a) =
      f.relativeDifferentialsDerivation.d (X := op U.1) a) :
    Function.Bijective e := by
  sorry

end AlgebraicGeometry
