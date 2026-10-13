/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.Differentials

/-! Compatibility of affine-chart transport for relative differentials with the derivation. -/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry
variable {X S : Scheme.{u}}

/-- The affine-chart differential comparison preserves the universal derivation.
Source: Stacks Project, Tags 01US and 01UT.
Proof: construct T as the composite displayed in its equality below. The inverse
of the base-open comparison sends d(b) to d(b), by relativeDifferentialsCompIso's
universal-property definition and relativeDifferentialsHomEquiv_symm_app_d.
Equality induction shows that relativeDifferentialsCongr does the same. The
inverse source-restriction comparison sends d(b) to the restricted derivation,
by relativeDifferentialsToRestrict_app_d. Composing these three identities proves
the assertion for every b. T is completely determined by the stated equality;
this theorem asserts neither surjectivity nor a property of a supplied linear map.
(blueprint: lem-sc-relative-differentials-affine-chart-derivation). -/
theorem relativeDifferentials_affine_chart_derivation (f : X ⟶ S)
    (U : X.affineOpens) (V : S.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1) :
    ∃ T : f.relativeDifferentials.restrict U.2.fromSpec ≅
        (Spec.map (f.appLE V.1 U.1 hUV)).relativeDifferentials,
      T = f.relativeDifferentialsRestrictIso U.2.fromSpec ≪≫
        Scheme.Hom.relativeDifferentialsCongr _
          (IsAffineOpen.SpecMap_appLE_fromSpec f V.2 U.2 hUV).symm ≪≫
        Scheme.Hom.relativeDifferentialsCompIso _ _ ∧
    ∀ b : Γ(Spec Γ(X, U.1), ⊤),
      T.inv.val.app (op ⊤)
        ((Spec.map (f.appLE V.1 U.1 hUV)).relativeDifferentialsDerivation.d b) =
          f.relativeDifferentialsDerivation.d ((U.2.fromSpec.appIso ⊤).inv b) := by
  sorry

end AlgebraicGeometry
