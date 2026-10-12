/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Comparing finite normal extensions on a dense open

Source: Stacks Project, Tag 0BQL, integral-closure argument.
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- Finite normal schemes are determined over a locally Noetherian base by their
restriction to an open whose preimage is dense in both sources.

Source: Stacks Project, Tag 0BQL, proof by integral closure, applied componentwise.
(blueprint: lem-sbc-finite-normal-dense-open-iso)

Proof: Work over an affine open Spec R of L. Finiteness gives affine inverse
images Spec B and Spec C. These are Noetherian normal rings: normality of all
local rings implies normality of the affine rings, and Noetherian normal rings
are finite products of integrally closed domains. The inverse image of U is
open dense in each source, so it contains every generic point. The given
isomorphism over U identifies the products of the fraction fields of B and C
as R-algebras. Both B and C are the integral closure of the image of R in this
common product: every element of either finite R-algebra is integral over R;
conversely, an element of the product integral over R is integral over B (or C)
and lies in B (or C), by integral closedness in the total ring of fractions.
Thus B and C agree inside that product and the resulting R-algebra isomorphism
extends the given isomorphism over U. The extension is unique, since a map into
a separated L-scheme is determined on a schematically dense open of a reduced
source. The affine isomorphisms therefore agree on intersections and glue.
If one source is empty, density and the restricted isomorphism force the other
source empty as well, and the same conclusion holds. -/
theorem finite_normal_iso_of_dense_open
    {L N E : Scheme.{u}} [IsLocallyNoetherian L]
    (n : N ⟶ L) (p : E ⟶ L) [IsFinite n] [IsFinite p]
    (hnormal : ∀ z : N, IsDomain (N.presheaf.stalk z) ∧
      IsIntegrallyClosed (N.presheaf.stalk z))
    (henormal : ∀ z : E, IsDomain (E.presheaf.stalk z) ∧
      IsIntegrallyClosed (E.presheaf.stalk z))
    (U : L.Opens)
    (hn : Dense (↑(n ⁻¹ᵁ U) : Set N))
    (hp : Dense (↑(p ⁻¹ᵁ U) : Set E))
    (e : (n ⁻¹ᵁ U).toScheme ≅ (p ⁻¹ᵁ U).toScheme)
    (he : e.hom ≫ (p ∣_ U) = n ∣_ U) :
    ∃ e' : N ≅ E, e'.hom ≫ p = n := by sorry

end AlgebraicGeometry.Scheme
