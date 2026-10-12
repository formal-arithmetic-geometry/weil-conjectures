/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.Differentials

/-!
# Differential sections on an affine chart

Source: Stacks Project, Tag 01UT.
(blueprint: lem-sc-relative-differentials-affine-sections).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- On an affine chart, differential sections are the ring's Kähler differentials,
compatibly with the universal derivation.
Source: Stacks Project, Tag 01UT; Tag 08S2, affine calculation.
(blueprint: lem-sc-relative-differentials-affine-sections).
Proof: restrict differentials along the open immersion of `U`, using
`relativeDifferentialsRestrictIso`. Factor the restricted morphism through `V` and use
`relativeDifferentialsCompIso` to remove the open immersion of the base. Identify `U`
and `V` with the spectra of their section rings, using their canonical affine
isomorphisms and `IsAffineOpen.SpecMap_appLE_fromSpec`. Apply
`relativeDifferentialsSpecΓIso` on global sections. The restriction formulas
`relativeDifferentialsToRestrict_app_d`, the derivation-preserving formula in
`relativeDifferentialsIsoOfDerivation`, and `relativeDifferentialsSpecΓHom_d` show
that the inverse of the resulting equivalence sends the ring differential of `a`
to the sheaf differential of `a`. Scalar transport is through the canonical section
ring isomorphisms, so this equivalence is linear over the original ring `Γ(X,U)`. -/
theorem relativeDifferentials_affine_sections (f : X ⟶ S)
    (U : X.affineOpens) (V : S.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1) :
    ∃ e : CommRingCat.KaehlerDifferential (f.appLE V.1 U.1 hUV) ≃ₗ[Γ(X, U.1)]
        Γ(f.relativeDifferentials, U.1),
      ∀ a : Γ(X, U.1), e (CommRingCat.KaehlerDifferential.d a) =
        f.relativeDifferentialsDerivation.d (X := op U.1) a := by sorry

end AlgebraicGeometry
