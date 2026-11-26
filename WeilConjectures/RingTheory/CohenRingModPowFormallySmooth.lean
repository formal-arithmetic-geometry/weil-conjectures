/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.Data.ZMod.Basic
public import WeilConjectures.RingTheory.CohenRing
import WeilConjectures.RingTheory.CohenRingModPowFormallySmoothCore
import WeilConjectures.RingTheory.CohenRingModPowFormallySmoothExplicit

/-!
# Formal smoothness of a Cohen ring modulo a prime power

A Cohen ring `Λ` modulo `p ^ n` is formally smooth over `ZMod (p ^ n)` for `n ≥ 1`.

## Implementation details

Formal smoothness is the square-zero lifting property `P(n)`. The case `P(1)` is lifting for
the residue field of characteristic `p`. Since `Λ` is torsion-free over `ℤ`, it is flat, so
`Λ/p^mΛ` is flat over `ℤ/p^mℤ`; formal smoothness then lifts along the square-zero ideal
`(p^n)` of `ℤ/p^(n+1)ℤ`, giving `P(n+1)`. Completeness is part of the Cohen-ring hypothesis but
is not used.

The `ZMod (p ^ n)`-algebra structure on the quotient exists and is unique, so the first clause of
`cohenRing_mod_pow_formallySmooth` quantifies over it instead of choosing one.

## References

* [Stacks, Tag 0327]
* [Stacks, Tag 0329]
* [Stacks, Tag 0322]
* [Stacks, Tag 031L]
-/

@[expose] public section

universe u v

namespace IsDiscreteValuationRing

/-- A Cohen ring modulo `p ^ n` is formally smooth over `ZMod (p ^ n)` for `n ≥ 1`. The first
clause is formal smoothness of `ℤ/p^n → Λ/p^nΛ`; the second spells out the same square-zero
lifting property for ring homomorphisms in an arbitrary target universe. -/
theorem cohenRing_mod_pow_formallySmooth
    (p : ℕ) (Λ : Type u) [CommRing Λ] (hΛ : IsCohenRing p Λ)
    (n : ℕ) (hn : 1 ≤ n) :
    (∀ [Algebra (ZMod (p ^ n)) (Λ ⧸ Ideal.span {(p : Λ) ^ n})],
      Algebra.FormallySmooth (ZMod (p ^ n)) (Λ ⧸ Ideal.span {(p : Λ) ^ n})) ∧
    (∀ (D : Type v) [CommRing D], (p : D) ^ n = 0 →
      ∀ (J : Ideal D), J ^ 2 = ⊥ →
        ∀ (g : (Λ ⧸ Ideal.span {(p : Λ) ^ n}) →+* D ⧸ J),
          ∃ f : (Λ ⧸ Ideal.span {(p : Λ) ^ n}) →+* D,
            (Ideal.Quotient.mk J).comp f = g) := by
  exact ⟨cohenRing_mod_pow_formallySmooth_core p Λ hΛ n hn,
    cohenRing_mod_pow_formallySmooth_explicit p Λ hΛ n hn⟩

end IsDiscreteValuationRing
