module

public import WeilConjectures.AlgebraicGeometry.Modules.Differentials

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- The universal derivation gives a linear map from affine Kähler differentials to
sections of relative differentials.  The affine comparison constructs this map.
Source: Stacks Project, Tag 01UT; the map part of the affine calculation.
(blueprint: lem-sc-relative-differentials-affine-sections-map).
-/
theorem relativeDifferentials_affine_sections_map (f : X ⟶ S)
    (U : X.affineOpens) (V : S.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1) :
    ∃ e : CommRingCat.KaehlerDifferential (f.appLE V.1 U.1 hUV) →ₗ[Γ(X, U.1)]
        Γ(f.relativeDifferentials, U.1),
      ∀ a : Γ(X, U.1), e (CommRingCat.KaehlerDifferential.d a) =
        f.relativeDifferentialsDerivation.d (X := op U.1) a := by
  sorry

end AlgebraicGeometry
