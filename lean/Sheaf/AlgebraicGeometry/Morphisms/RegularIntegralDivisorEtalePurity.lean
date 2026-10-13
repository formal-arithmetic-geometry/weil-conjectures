/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.Regular
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Purity across a regular integral effective Cartier divisor

Source: Stacks Project, Tag 0EYE; Tag 0EYJ, second paragraph.
(blueprint: lem-sbc-regular-integral-divisor-etale-purity)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- A finite cover, etale off a regular integral Cartier divisor and near its
unique generic point, has a finite etale extension of its restriction.

Source: Stacks Project, Tag 0EYE (Lemma 58.31.3), applied as in Tag 0EYJ.
(blueprint: lem-sbc-regular-integral-divisor-etale-purity)

Proof: The Cartier hypothesis makes the complement U dense in L. At every
point of D, the local ring of L is Noetherian and its quotient by the Cartier
nonzerodivisor is the regular local ring of D. Regularity lifts across this
nonzerodivisor (Stacks Tag 00NU), so L is regular along D. At the generic
point of D the quotient is a field, hence the local ring of L is a DVR.
At any other point of D that quotient has positive dimension, so the local
ring of L has dimension at least two. Thus the generic point of D is the
only codimension-one point of L outside U. Over W the finite etale restriction of n provides an
extension of the cover over U near this point; after base change to its DVR
local ring this is an unramified extension. Thus n restricted to U is
unramified over L in codimension one. Apply Tag 0EYE to obtain a finite etale
p over L with restriction isomorphic to n restricted to U. Invert the
isomorphism if necessary so its hom points from the restriction of n to the
restriction of p. Being an isomorphism over U is exactly the composition
identity displayed below. This does not require L to be quasi-compact or
quasi-separated. The empty cover also satisfies the purity theorem. -/
theorem exists_finite_etale_extension_of_regular_integral_divisor
    {L D N : Scheme.{u}} [IsLocallyNoetherian L] [IsRegular D] [IsIntegral D]
    (i : D ⟶ L) (hi : IsEffectiveCartierCenter i)
    (U : L.Opens) (hU : ∀ z : L, z ∈ U ↔ z ∉ Set.range i)
    (n : N ⟶ L) [IsFinite n] (het : Etale (n ∣_ U))
    (W : L.Opens) (hgeneric : i (genericPoint D) ∈ W) (hW : Etale (n ∣_ W)) :
    ∃ (E : Scheme.{u}) (p : E ⟶ L), IsFinite p ∧ Etale p ∧
      ∃ e : (n ⁻¹ᵁ U).toScheme ≅ (p ⁻¹ᵁ U).toScheme,
        e.hom ≫ (p ∣_ U) = n ∣_ U := by sorry

end AlgebraicGeometry.Scheme
