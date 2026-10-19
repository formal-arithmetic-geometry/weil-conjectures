/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q131
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Sheaf.RingTheory.CoverModuleExact

/-!
# Complementary quotient for idempotent localizations away from an ideal

Source: Stacks Project, More on Algebra, Tag 0C2A, `lemma-glueing-sum-components-open`
(blueprint: lem-per-punctured-idempotent-complement).
-/

@[expose] public section

universe u v

namespace RingTheory

/-- A ring map which is an idempotent localization away from a finitely generated ideal
has a complementary quotient on that punctured locus. The algebra structure in `hlocal`
is explicitly induced by `Localization.awayMap u f`, so the localization assertion concerns
that structural map. Bijectivity in the conclusion says that the specified ring map is an
isomorphism. The quotient ring may be chosen in the universe of `R`.

Source: Stacks Project, More on Algebra, Tag 0C2A, `lemma-glueing-sum-components-open`
(blueprint: lem-per-punctured-idempotent-complement).

Proof:
1. Choose generators `f₁, ..., fᵣ` of `K`. If the list is empty, `K = 0`; take `E' = R`
   and the identity quotient. The only element to invert is zero, giving zero rings on
   both sides, by the fraction relation of `def-weil-ring-localization-away`.
2. Otherwise write the given local idempotents as `eᵢ = aᵢ/fᵢ^nᵢ`. Clear the finitely many
   idempotence relations by multiplying the numerators and denominators by further powers
   of `fᵢ`, then take a common exponent `n`. This gives `aᵢ² = fᵢ^n aᵢ` in `R`.
3. On `R_(fᵢ fⱼ)` the two idempotents coincide: both describe the same map to `E_(fᵢ fⱼ)`.
   Indeed the image of `eᵢ` in the localization at `eⱼ` is 1. Clearing the denominator and
   using idempotence yields `eᵢ eⱼ = eⱼ`; interchanging indices yields `eᵢ eⱼ = eᵢ`.
   Iterated localization and these equalities use `def-weil-ring-localization-away`.
4. Clear the finitely many overlap equalities with one exponent `N`. Set `bᵢ = fᵢ^N aᵢ`
   and `d = n + N`. Then `fⱼ^d bᵢ = fᵢ^d bⱼ`, `bᵢ² = fᵢ^d bᵢ`, and `eᵢ = bᵢ/fᵢ^d`.
   Thus in `R_fᵢ` each `bⱼ` is a multiple of `bᵢ`.
5. Let `J = (b₁, ..., bᵣ)` and take the surjection `R → E' = R/J`.
   By `lem-weil-pbc-localization-quotient-commute`, `E'_fᵢ = R_fᵢ/(eᵢ)` compatibly with
   the quotient map.
6. For an idempotent `e` of `B`, the canonical map `B → B_e × B/(e)` is an isomorphism:
   identify the factors with `eB` and `(1-e)B`, respectively, and use `(x,y) ↦ x+y`
   as inverse. Together with the given identification of `E_fᵢ`, this proves the result
   at each generator.
7. Localization commutes with a two-factor product: fractions map componentwise, and
   `(x/h^k,y/h^l)` has inverse image `(h^l x,h^k y)/h^(k+l)`.
   These fraction formulas identify the map in step 6 with `Localization.awayMap (u.prod v)`
   and show that further localization preserves the isomorphisms.
8. For any `f ∈ K`, the images of the generators generate the unit ideal in `R_f`.
   Apply `lem-weil-pbc-cover-module-exact` to `R_f` and `(E × E')_f`, using the module
   localizations of `def-weil-pbc-module-localization-away`. Its injectivity clause detects
   a zero kernel; its gluing clause glues the inverse images of any target element, and
   injectivity detects that the glued image is that element. This proves bijectivity for
   every `f ∈ K`, not only for the chosen generators. -/
theorem exists_punctured_idempotent_complement
    {R : Type u} [CommRing R] {E : Type v} [CommRing E]
    (K : Ideal R) (hK : K.FG) (u : R →+* E)
    (hlocal : ∀ f ∈ K, ∃ e : Localization.Away f, IsIdempotentElem e ∧
      @IsLocalization.Away (Localization.Away f) _ e (Localization.Away (u f)) _
        (Localization.awayMap u f).toAlgebra) :
    ∃ (E' : Type u) (_ : CommRing E') (v : R →+* E'), Function.Surjective v ∧
      ∀ f ∈ K, Function.Bijective (Localization.awayMap (u.prod v) f) := by
  sorry

end RingTheory
