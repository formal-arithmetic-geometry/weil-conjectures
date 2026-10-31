/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.SetTheory.Cardinal.Subfield

/-!
# Algebraically closed extensions with large transcendence degree

Source: Stacks Project, Tag 04LR, proof of `lemma-groupoid-on-field-explain-points`,
construction (1), expanded using cardinal enlargement and transcendence bases
(blueprint: lem-sfb-large-algclosed-field-extension).
-/

@[expose] public section

universe u

namespace Field

/-- Every field embeds in an algebraically closed field whose cardinal transcendence degree
over its prime subfield exceeds both its cardinality and the countable cardinal.
The prime subfield is the bottom subfield; the embedding is `algebraMap E K`.

Source: Stacks Project, Tag 04LR, proof of `lemma-groupoid-on-field-explain-points`,
construction (1) (blueprint: lem-sfb-large-algclosed-field-extension).

Proof plan:
1. In the common universe put `κ = max ℵ₀ #E` and let `λ` be its successor cardinal.
   Cantor's theorem ensures `κ < λ`, and `λ` is infinite.
2. Apply `lem-sfb-algclosed-extension-cardinal-lower-bound` to obtain an algebraically
   closed extension `K/E` with `λ ≤ #K`. Its structural ring homomorphism is injective
   because its domain is a field (`def-pc-field-extension`). Thus `K` is uncountable.
3. The prime subfield `P` is countable by `lem-sfb-prime-subfield-countable`.
   Choose a transcendence basis `b : I → K` over `P` using
   `lem-exc-transcendence-basis-exists`. The countable-base, uncountable algebraically
   closed-field cardinality theorem `lem-weil-countable-base-transcendence-cardinality`
   gives `#I = #K`. By `def-kun-transcendence-degree`, `Algebra.trdeg P K = #I`.
4. Combine `max ℵ₀ #E < λ ≤ #K = Algebra.trdeg P K`. All cardinals and both fields
   belong to the same universe. -/
theorem exists_algClosed_extension_large_prime_trdeg (E : Type u) [Field E] :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra E K),
      IsAlgClosed K ∧
        max Cardinal.aleph0 (Cardinal.mk E) < Algebra.trdeg (↥(⊥ : Subfield K)) K := by
  sorry

end Field
