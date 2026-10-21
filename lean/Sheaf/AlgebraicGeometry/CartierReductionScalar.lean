/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T3
-/
module

public import Sheaf.AlgebraicGeometry.GeoCartierCanonicalClass

/-! # Naturality of the normalized Cartier reduction

Source: blueprint main-20261015, sk-lem-geo-cartier.proof.md.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

/-- Reduction of the integral pole boundary commutes with an arbitrary finite
coefficient homomorphism, including a nonflat one.
Source: blueprint sk-lem-geo-cartier.proof.md, paragraph 4, finite coefficient extension;
(blueprint: lem-sfb-cartier-reduction-scalar).
Proof: the supported constant has integral stalk Z on D and zero off D. Its derived
extension to A is therefore the supported A-constant, with unit sending one to one.
The roots line is locally free of rank one over Z/n, so its further derived extension
is the ordinary tensor line, without assuming flatness of B over A. The scalar units
are determined on constant generators and pure root tensors. Their Hom adjunctions
hold against every unbounded complex by the derived scalar adjunction. Transitivity
of derived extension identifies the two extensions of the integral pole boundary.
The tensor associativity map sends (x tensor a) tensor b to x tensor phi(a)b, giving
both displayed normalizations. Apply the comparison inverse image; its scalar
comparison preserves these units. The relative-boundary uniqueness
identifies these reductions with the canonical ordinary classes. Their canonical
comparison equations then give the asserted pro-etale Ext square.
Empty support and the zero coefficient ring give zero objects; the identity ring map
recovers the identity units and the reflexive square. -/
theorem geoCartierCanonicalClass_scalar (A B : Type (u + 1)) [CommRing A] [CommRing B]
    [Finite A] [Finite B] (n : ℕ) (hn : 0 < n) (hA : (n : A) = 0)
    (hB : (n : B) = 0) (φ : A →+* B) {D Z : Scheme.{u}} (i : D ⟶ Z)
    [IsClosedImmersion i] (hI : i.ker.IsInvertible) (hZ : IsUnit (n : Γ(Z, ⊤))) :
    GeoCartierScalarCompatibility φ n hA hB i
      (geoCartierCanonicalClass A n hn hA i hI hZ)
      (geoCartierCanonicalClass B n hn hB i hI hZ) := by
  sorry

end AlgebraicGeometry.ProEtale
