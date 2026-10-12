/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X2
-/
module

public import Sheaf.Algebra.Homology.TotalFreeFiltrationEvenQuotientMap

/-!
# Degreewise bijectivity of the even column quotient map

Source: Stacks Project, Tag 09KP, alternating column filtration.
(blueprint: lem-pc-derived-total-filtration-even-quotient-bijective)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex.TotalFreeFiltration

variable {A : Type u} [CommRing A]
variable (K : HomologicalComplex₂ (ModuleCat.{u} A) (ComplexShape.up ℤ) (ComplexShape.up ℤ))
variable (S : ℕ → ShortComplex (CochainComplex (ModuleCat.{u} A) ℤ))
variable (e : ∀ j : ℕ, (S j).X₂ ≅ K.X (-(j : ℤ)))
variable (h_positive : ∀ p : ℤ, 0 < p → IsZero (K.X p))

/-- The explicit degree map into the even quotient is bijective.
Source: Stacks Project, Tag 09KP, proof, successive column quotients.
(blueprint: lem-pc-derived-total-filtration-even-quotient-bijective)

Proof. Evaluation preserves cokernels, so identify the evaluated categorical
cokernel with the quotient of term (2j+1) k by term (2j) k. The earlier lower
pieces lie in their full columns. Thus term (2j) k is the sum of the full
columns -a with a<j, and term (2j+1) k adds precisely the image of lower j k.
This proves surjectivity of the displayed map. The total degree object is the
coproduct of its column degree objects; its coordinate projection onto column
-j vanishes on every earlier full column and is a left inverse of full j k.
Consequently the range of lower j k intersects term (2j) k trivially. The
first arrow of the short exact complex S j is degreewise injective, e j is an
isomorphism, and full j k is injective by the coordinate projection. A vector
whose image in the quotient is zero therefore was zero, proving injectivity.
The categorical cokernel comparison is an isomorphism and transports both
claims to the specified map. Empty earlier-column sums (j=0), zero modules,
and zero coefficient rings cause no exception. No basis or splitting is used.
-/
theorem evenQuotientComponent_bijective
    (h_exact : ∀ j, (S j).ShortExact) (j : ℕ) (k : ℤ) :
    Function.Bijective (evenQuotientComponent K S e h_positive j k) := by sorry

end CochainComplex.TotalFreeFiltration
