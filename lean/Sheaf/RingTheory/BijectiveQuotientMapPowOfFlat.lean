/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Isomorphisms modulo powers of an ideal under a flat ring map

Source: Stacks Project, More on Algebra, proof of Tag 0AGU, using Algebra, Tag 051H
(blueprint: lem-weil-pbc-flat-iso-mod-ideal-powers).
-/

universe u v

namespace RingHom

/-- A flat ring map that induces an isomorphism modulo an ideal induces an isomorphism
modulo every positive power of that ideal. Here `Ideal.map` is extension of the ideal,
and bijectivity of the induced ring homomorphism expresses that this map is an isomorphism.
Source: Stacks Project, proof of Tag 0AGU, referring to Tag 051H
(blueprint: lem-weil-pbc-flat-iso-mod-ideal-powers).

Proof: Write βₙ for the induced map on quotients and αₙ for the induced map
`I^n / I^(n+1) → I^n B / I^(n+1) B`. The inclusion and reduction maps give two short
exact rows with vertical maps αₙ, βₙ₊₁, βₙ, and the squares commute.
Surjectivity of β₁ gives `B = φ(A) + IB`. Writing each coefficient of a generator
`φ(x)b` of `I^n B` in this form gives `I^n B = φ(I^n) + I^(n+1) B`, so αₙ is surjective.
For injectivity, put `N = I^n / I^(n+1)`, annihilated by I. The inverse of β₁ defines
an A-linear retraction of `N → N ⊗[A] B`, by sending `x ⊗ b` to `β₁⁻¹(b mod IB) • x`.
Flatness (def-weil-pbc-flat-ring-map) makes the tensor of `N → A/I^(n+1)` injective.
The tensor-quotient isomorphism (lem-weil-pbc-tensor-quotient-base-change) identifies
its target with `B/I^(n+1) B`. The composite on N is the inclusion composed with αₙ,
so αₙ is injective. Starting with β₁, induction and the short five lemma
(lem-weil-pbc-short-five-lemma) now show that every βₙ for n ≥ 1 is bijective.
A bijective ring homomorphism has an additive and multiplicative inverse. -/
theorem bijective_quotientMap_pow_of_flat {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] (φ : A →+* B) (hφ : φ.Flat) (I : Ideal A)
    (hI : Function.Bijective (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map)) :
    ∀ n : ℕ, 1 ≤ n → Function.Bijective
      (Ideal.quotientMap ((I ^ n).map φ) φ Ideal.le_comap_map) := by
  sorry

end RingHom
