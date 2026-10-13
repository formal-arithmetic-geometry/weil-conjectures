/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RelativeDifferentialsAffineSectionsMap
import WeilConjectures.AlgebraicGeometry.Modules.Differentials

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry
variable {X S : Scheme.{u}}

/-- The affine comparison map is surjective by the affine calculation for relative
differentials. Identify the affine open with a spectrum, use the canonical affine
comparison for relative differentials, and transport its surjectivity to sections.
Source: Stacks Project, Tag 01UT.
(blueprint: lem-sc-relative-differentials-affine-sections-map-surjective). -/
theorem relativeDifferentials_affine_sections_map_surjective (f : X ⟶ S)
    (U : X.affineOpens) (V : S.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1)
    (e : CommRingCat.KaehlerDifferential (f.appLE V.1 U.1 hUV) →ₗ[Γ(X, U.1)]
      Γ(f.relativeDifferentials, U.1))
    (he : ∀ a : Γ(X, U.1), e (CommRingCat.KaehlerDifferential.d a) =
      f.relativeDifferentialsDerivation.d (X := op U.1) a) : Function.Surjective e := by
  sorry
end AlgebraicGeometry
