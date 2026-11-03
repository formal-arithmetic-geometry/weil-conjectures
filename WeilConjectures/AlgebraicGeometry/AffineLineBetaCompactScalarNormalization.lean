/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CoefficientCompatibility.EtaleProEtaleCoefficientCompatibility2
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
import WeilConjectures.AlgebraicGeometry.AffineLineBetaOpenMapNormalization
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale
/-- The interface beta map agrees with the canonical compact-support scalar mate.
Source: the coefficient compatibility normalization in the current interface route.
The two maps are defined by the same proper mate and normalized open comparison;
expanding the adjunction presentations and applying mate uniqueness proves equality
componentwise. (blueprint: lem-sp-affine-line-canonical-scalar-counit). -/
theorem affineLineBetaCompactScalarNormalization
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (L : DerivedCategoryModule A X) :
    (ProEtale.CoefficientCompatibility.beta φ c).app L =
      (compactScalarMap φ c).app L := by
  sorry
end AlgebraicGeometry.Etale
