/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CoefficientCompatibility.EtaleProEtaleCoefficientCompatibility2
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale
/-- The current interface open comparison is the normalized exceptional open map.
Source: the open scalar adjunction normalization in the coefficient compatibility route;
expand both left-adjoint uniqueness constructions and cancel the common scalar mate.
(blueprint: lem-sp-affine-line-canonical-scalar-counit). -/
theorem affineLineBetaOpenMapNormalization
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j]
    (L : DerivedCategoryModule A U) :
    (ProEtale.CoefficientCompatibility.etOpen φ j).hom.app L =
      (ExceptionalCoefficients.openIso φ j).hom.app L := by
  sorry
end AlgebraicGeometry.Etale
