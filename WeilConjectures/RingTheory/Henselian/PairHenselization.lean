/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.Unramified.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.CategoryTheory.Filtered.FinallySmall
public import Mathlib.CategoryTheory.Limits.FinallySmall
public import Mathlib.Algebra.Category.Ring.FilteredColimits

/-!
# The henselization of a pair

Let `B` be a commutative ring and `J` an ideal of `B`. An *étale neighbourhood* of `V(J)` is an
étale `B`-algebra `S` together with a `B`-algebra map `σ : S → B ⧸ J`. These form a filtered,
finally small category, and the colimit `Bʰ` of the algebras `S` is the henselization of the pair
`(B, J)`: the pair `(Bʰ, JBʰ)` is henselian and `B ⧸ J → Bʰ ⧸ JBʰ` is bijective.

## Main definitions

- `PairHenselization.Nbhd B J`: the category of étale neighbourhoods.
- `PairHenselization.henselization B J`: the colimit `Bʰ`.

## Main statements

- `PairHenselization.henselianRing`: `(Bʰ, JBʰ)` is a henselian pair.
- `PairHenselization.bijective_quotientMap`: `B ⧸ J ≅ Bʰ ⧸ JBʰ`.

## References

- Stacks Project, Lemma 15.12.1, <https://stacks.math.columbia.edu/tag/0A02>
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace PairHenselization

variable (B : Type u) [CommRing B] (J : Ideal B)

/-- An étale neighbourhood of `V(J)` in `Spec B`: an étale `B`-algebra `S` with a `B`-algebra
map `σ : S → B ⧸ J`. -/
structure Nbhd where
  /-- the étale `B`-algebra -/
  S : Type u
  [commRing : CommRing S]
  [algebra : Algebra B S]
  [etale : Algebra.Etale B S]
  /-- the section over `V(J)` -/
  σ : S →ₐ[B] B ⧸ J

/-- The henselization `Bʰ` of the pair `(B, J)`: the colimit of the étale neighbourhoods of
`V(J)`. -/
noncomputable def henselization (B : Type u) [CommRing B] (J : Ideal B) : Type u :=
  sorry

noncomputable instance : CommRing (henselization B J) :=
  sorry

noncomputable instance : Algebra B (henselization B J) :=
  sorry

/-- The henselization of a pair is a henselian pair. -/
instance henselianRing :
    HenselianRing (henselization B J) (J.map (algebraMap B (henselization B J))) :=
  sorry

/-- The henselization does not change the quotient: `B ⧸ J ≅ Bʰ ⧸ JBʰ`. -/
theorem bijective_quotientMap :
    Function.Bijective (Ideal.quotientMap (J.map (algebraMap B (henselization B J)))
      (algebraMap B (henselization B J)) Ideal.le_comap_map) :=
  sorry

end PairHenselization
