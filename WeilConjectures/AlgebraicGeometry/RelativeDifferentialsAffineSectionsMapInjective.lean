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

/-- The affine comparison map is injective by the uniqueness part of the universal
property of Kähler differentials. Apply the affine Spec comparison to identify the
target with the module of Kähler differentials, then use uniqueness of maps preserving
the universal derivation. Source: Stacks Project, Tag 01UT.
(blueprint: lem-sc-relative-differentials-affine-sections-map-injective). -/
theorem relativeDifferentials_affine_sections_map_injective (f : X ⟶ S)
    (U : X.affineOpens) (V : S.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1)
    (e : CommRingCat.KaehlerDifferential (f.appLE V.1 U.1 hUV) →ₗ[Γ(X, U.1)]
      Γ(f.relativeDifferentials, U.1))
    (he : ∀ a : Γ(X, U.1), e (CommRingCat.KaehlerDifferential.d a) =
      f.relativeDifferentialsDerivation.d (X := op U.1) a) : Function.Injective e := by
  sorry
end AlgebraicGeometry
