/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.RegularDivisor
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Principal regular divisors of affine schemes

For a ring `S` and a non-zero-divisor `a ∈ S` with `S/(a)` regular, the closed immersion
`Spec (S/(a)) ⟶ Spec S` is a regular divisor; two such divisors `V(a)`, `V(b)` meet transversely
at a single point if `S/(a, b)` is a field.

## Main results

- `AlgebraicGeometry.isRegular_spec`: the spectrum of a regular ring is regular.
- `AlgebraicGeometry.isRegularDivisor_specMap_quotient`: `Spec (S/(a)) ⟶ Spec S` is a regular
  divisor.
- `AlgebraicGeometry.meetTransverselyAt_specMap_quotient`: `V(a)` and `V(b)` meet transversely at
  the point `V(a, b)` when `S/(a, b)` is a field.
- `AlgebraicGeometry.range_specMap_quotient`: the image of `Spec (S/I) ⟶ Spec S` is `V(I)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {S : Type u} [CommRing S]

/-- The spectrum of a regular ring is a regular scheme. -/
lemma isRegular_spec [IsRegularRing S] : IsRegular (Spec (.of S)) :=
  sorry

/-- The image of the closed immersion `Spec (S/I) ⟶ Spec S` is the zero locus of `I`. -/
lemma range_specMap_quotient (I : Ideal S) :
    Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) =
      PrimeSpectrum.zeroLocus (I : Set S) :=
  sorry

/-- For a non-zero-divisor `a ∈ S` with `S/(a)` regular, `Spec (S/(a)) ⟶ Spec S` is a regular
divisor. -/
lemma isRegularDivisor_specMap_quotient {a : S} (ha : a ∈ nonZeroDivisors S)
    [IsRegularRing (S ⧸ Ideal.span {a})] :
    IsRegularDivisor (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a})))) :=
  sorry

/-- If `S/(a, b)` is a field `K`, the closed subschemes `V(a)` and `V(b)` of `Spec S` meet
transversely at the single point `V(a, b)`. -/
lemma meetTransverselyAt_specMap_quotient {a b : S} (hab : IsField (S ⧸ Ideal.span {a, b}))
    (z : Spec (.of S)) (hz : z.asIdeal = Ideal.span {a, b}) :
    MeetTransverselyAt (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a}))))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {b})))) z :=
  sorry

end AlgebraicGeometry
