/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-! # Conjugating embeddings of a small field

Source: Stacks Project, Tag 04LR, `more-groupoids.tex`, proof of
`lemma-groupoid-on-field-explain-points`, construction (3).
(blueprint: lem-sfb-small-field-embeddings-conjugate)
-/

@[expose] public section

universe u v

namespace IsAlgClosed

/-- Two embeddings of a field into an algebraically closed field of sufficiently large
transcendence degree are conjugate by an automorphism of the latter field.

Source: Stacks Project, Tag 04LR, `more-groupoids.tex`, proof of
`lemma-groupoid-on-field-explain-points`, construction (3).
(blueprint: lem-sfb-small-field-embeddings-conjugate)

Proof: Put μ = max(ℵ₀, |F|) and λ = trdeg over the prime subfield of K. The definition
of transcendence degree bounds λ by |K|, so μ < |K|. Use
`lem-exc-transcendence-basis-exists` separately for the F-algebra structures on K given
by a and b, obtaining bases x indexed by I and y indexed by J. The bound
`lem-sfb-algclosed-transcendence-basis-cardinal-bound` gives
|K| ≤ max(μ, |I|) and |K| ≤ max(μ, |J|). Since both index sets are subsets of K,
these inequalities and μ < |K| imply |I| = |J| = |K|, even when |K| is singular.
Choose a bijection e : I ≃ J.

Algebraic independence, as in `def-weil-pbc-transcendence-basis`, makes coefficient
and variable substitution a well-defined isomorphism between the polynomial subrings:
replace a(c) by b(c) and x(i) by y(e(i)). Reverse substitution gives its inverse.
Extend it to the subfields L = a(F)(x) and M = b(F)(y) by sending a fraction r/s to
f(r)/f(s). Injectivity preserves nonzero denominators, and cross-multiplication
proves well-definedness. Reverse substitution again gives the inverse.

By `lem-exc-transcendence-basis-algebraic-closure`, K is an algebraic closure of
both L and M. Twist the target L-algebra structure by the constructed isomorphism
h : L ≃ M. Algebraicity is preserved: pull each polynomial relation over M back
coefficientwise through h inverse. By clause (2) of
`lem-pc-algebraic-closure-exists-unique`, the two algebraic closures of L are
isomorphic over L. Their underlying field isomorphism τ : K ≃ K satisfies
τ(a(c)) = b(c) for every c : F, hence τ composed with a equals b.
-/
theorem exists_ringEquiv_comp_eq_of_small
    (F : Type u) (K : Type v) [Field F] [Field K] [IsAlgClosed K]
    (a b : F →+* K)
    (hsmall : max Cardinal.aleph0 (Cardinal.lift.{v} (Cardinal.mk F)) <
      Cardinal.lift.{u} (Algebra.trdeg (⊥ : Subfield K) K)) :
    ∃ τ : K ≃+* K, τ.toRingHom.comp a = b := by
  sorry

end IsAlgClosed
