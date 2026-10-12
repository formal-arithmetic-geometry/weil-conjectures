/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E2
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

import Sheaf.RingTheory.EtaleNormalRing

/-!
# Comparing a normal finite cover with a finite etale cover

Source: Stacks Project, Tags 035I, 035L and 0BQM; the comparison in Tag 0EYJ.
(blueprint: lem-sbc-finite-normal-dense-open-comparison)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- A normal finite cover agrees with a finite etale cover if they agree on a dense open.

Source: Stacks Project, Tags 035I and 035L (relative normalization), Tag 0BQM
(integral-closure description), and the comparison in Tag 0EYJ.
(blueprint: lem-sbc-finite-normal-dense-open-comparison)

Proof: On an affine open Spec R of the normal integral base B, the two finite
covers are Spec C and Spec D. They are Noetherian and normal: normality of C comes
from hN; normality of D ascends through the etale ring map by 033C. A normal
Noetherian ring is a finite product of integrally closed domains. Density of
n^{-1} U ensures every component of C meets this open. As n is etale there, each
such component dominates the integral base: the etale image of its nonempty open
part is open and contains the generic point. The components of D also dominate,
since a finite etale morphism is flat and open. Since U is nonempty, it contains
the generic point of B. The given isomorphism over U therefore identifies the
finite generic algebras of C and D. In every component C is precisely the integral
closure of R in its generic field: its elements are integral over R by finiteness;
conversely an element integral over R is integral over C and belongs to C by
integral closedness. The same holds for D. Hence the generic isomorphism identifies
C with D. These affine identifications agree on overlaps because their generic
restrictions agree and both algebras inject into their generic algebras. They glue
to the stated isomorphism e over B. For empty covers the zero algebras are identified;
no connectedness or surjectivity of either cover is required. This comparison does
not construct an etale extension of an open cover. -/
theorem finite_normal_iso_of_dense_open_etale_comparison
    {B N E : Scheme.{u}} [IsLocallyNoetherian B] [IsIntegral B]
    (hB : ∀ y : B, IsIntegrallyClosed (B.presheaf.stalk y))
    (n : N ⟶ B) (p : E ⟶ B) [IsFinite n] [IsFinite p] [Etale p]
    (hN : ∀ z : N, IsDomain (N.presheaf.stalk z) ∧
      IsIntegrallyClosed (N.presheaf.stalk z))
    (U : B.Opens) (hU : (U : Set B).Nonempty)
    (hdense : Dense (↑(n ⁻¹ᵁ U) : Set N))
    (hnU : Etale (n ∣_ U))
    (eU : (n ⁻¹ᵁ U).toScheme ≅ (p ⁻¹ᵁ U).toScheme)
    (heU : eU.hom ≫ p ∣_ U = n ∣_ U) :
    ∃ e : N ≅ E, e.hom ≫ p = n := by sorry

end AlgebraicGeometry.Scheme
