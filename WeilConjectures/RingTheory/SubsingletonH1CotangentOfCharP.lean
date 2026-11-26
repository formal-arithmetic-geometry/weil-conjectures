/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.RingTheory.Extension.Cotangent.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.Smooth.Field
import WeilConjectures.RingTheory.H1CotangentFiniteSubfields

/-!
# Vanishing of the first cotangent homology of a field over its positive prime field

For a field `K` of positive characteristic `p`, the first homology of the naive cotangent
complex of `K` over `𝔽_p` vanishes (`Algebra.subsingleton_h1Cotangent_of_charP`).

## Implementation details

A cycle involves only finitely many variables, so the statement reduces to finitely generated
subfields `E` of `K` (`subsingleton_h1Cotangent_of_finite_subfields`). Such an `E` is
essentially of finite type over the perfect field `𝔽_p`, hence formally smooth, and its first
cotangent homology vanishes.

## References

* [Stacks, Tag 0322], characteristic `p`, (1) ⇒ (5), with `k = 𝔽_p`
* [Stacks, Tag 07E5], proof of (3) ⇔ (4)
-/

@[expose] public section

universe u

namespace Algebra

/-- For a field `K` of positive characteristic `p`, the first homology of the naive
cotangent complex of the canonical presentation `𝔽_p[K] → K` is zero. The algebra
structure is the unique one, supplied by `ZMod.algebra K p`. -/
theorem subsingleton_h1Cotangent_of_charP
    (p : ℕ) (hp : 0 < p) (K : Type u) [Field K] [CharP K p] :
    letI := ZMod.algebra K p
    Subsingleton (H1Cotangent (ZMod p) K) := by
  have : Fact p.Prime := ⟨CharP.char_prime_of_ne_zero K (Nat.ne_of_gt hp)⟩
  let := ZMod.algebra K p
  apply subsingleton_h1Cotangent_of_finite_subfields
  intro E hE
  have : Algebra.EssFiniteType (ZMod p) E := IntermediateField.essFiniteType_iff.mpr hE
  exact Algebra.FormallySmooth.subsingleton_h1Cotangent

end Algebra
