/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T3
-/
module

public import Sheaf.AlgebraicGeometry.GeoCartierCanonicalClass

/-! # The Cartier Chern equation under comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- The normalized ordinary Cartier boundary satisfies the pro-etale Chern equation.
Source: blueprint sk-lem-geo-cartier.proof.md, paragraphs 1 and 5
(blueprint: lem-sfb-geo-cartier-canonical-chern).
Proof: ordinary_supported_kummer supplies a boundary representative and its Kummer
Chern class. Uniqueness identifies that representative with geoCartierEtaleClass.
For a closed immersion, the exact direct-image comparison intertwines the degree-zero
constant unit with supportedDerivedUnit; its single-complex comparison intertwines
supportedExactDerivedMap with Ext.homEquiv. Thus the ordinary unit equation is the
Yoneda equation obtained by precomposition with the ordinary supported constant unit.
The comparison mate commutes with units, by the two adjunction triangle identities.
Apply exact comparison inverse image to this equation, identify the constants by
comparisonUpperStarConstantSheafIso, and cancel the invertible supported-source mate.
The resulting equation is precisely GeoCartierChernEquation, with the same ordinary
Chern witness and the same integral generator. No sign is changed: the pole frame is
the inverse Cartier equation, the frame of the dual ideal. For empty support both
sides are zero; for the zero coefficient ring all objects and equations are zero.
-/
theorem geoCartierCanonicalClass_chern (A : Type (u + 1)) [CommRing A] [Finite A]
    (n : ℕ) (hn : 0 < n) (hA : (n : A) = 0) {D Z : Scheme.{u}}
    (i : D ⟶ Z) [IsClosedImmersion i] (hI : i.ker.IsInvertible)
    (hZ : IsUnit (n : Γ(Z, ⊤))) :
    GeoCartierChernEquation A n hA i hI hZ
      (geoCartierCanonicalClass A n hn hA i hI hZ) := by
  sorry

end AlgebraicGeometry.ProEtale
