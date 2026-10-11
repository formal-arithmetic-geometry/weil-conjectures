/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Gabber's polynomial for a finite algebra over a Zariski pair

Source: Stacks Project, More on Algebra, Lemma Tag 0EM0 (lemma-helper-finite)
(blueprint: lem-weil-pbc-zariski-pair-finite-gabber-polynomial).
-/

@[expose] public section

universe u v w z

open Polynomial
open scoped BigOperators

namespace Algebra

/-- A lift of `(1,0)` in a finite algebra over a Zariski pair is annihilated by a monic
polynomial of the form `X^d (X-1) + ∑ aⱼ X^j`, with `d ≥ 1` and `aⱼ ∈ I`.
The compatibility condition on `e` says that the quotient decomposition is one of
`A/I`-algebras, rather than merely of rings.
Source: Stacks Project, More on Algebra, Lemma Tag 0EM0 (lemma-helper-finite).
(blueprint: lem-weil-pbc-zariski-pair-finite-gabber-polynomial)

Proof (the ten steps of the DAG node):
1. Finiteness implies integrality (`lem-weil-pbc-finite-algebra-is-integral`). Lift the
idempotent `(1,0)` after an étale extension `A → A'` preserving `A/I`, using
`lem-weil-pbc-lift-idempotent-upstairs` (Tag 07M4).
2. Decompose `B ⊗[A] A'` using this lifted idempotent into finite factors `B'₁ × B'₂`.
The image of `b` is congruent to `1` in the first factor and `0` in the second.
3. The finite cokernel of `A' → B'₁` vanishes modulo `IA'`. Nakayama gives `g ∈ 1+IA'`
annihilating it (`lem-weil-pbc-nakayama-one-plus-ideal-annihilator`, Tag 00DV).
4. Localize at `g`, obtaining `A'' → B''₁` surjective and still `A/I ≅ A''/IA''`.
Flatness follows from `lem-weil-pbc-etale-algebra-flat`,
`lem-weil-pbc-localization-flat` and `lem-weil-pbc-flat-ring-map-comp`.
5. Choose `a' ∈ IA''` mapping to `b''₁-1` by this surjection.
6. By `lem-weil-pbc-finite-algebra-is-integral` and
`lem-weil-pbc-integral-extended-ideal-element-monic` (Tag 00H5), choose a monic
polynomial annihilating `b''₂` and reducing to a power of `X`. Multiply it by `X`
so that its degree `d` is at least one, including when the second factor is zero.
7. Multiply this polynomial by `X-1-a'`. It annihilates `b''` and yields
`(b''-1)b''^d ∈ ∑ⱼ IA'' b''^j`, with `0 ≤ j ≤ d`.
8. Every maximal ideal of `A` contains `I`, and its fibre in `A''` is nonzero since
`A/I ≅ A''/IA''`. Thus `A → A''` is faithfully flat by
`lem-weil-pbc-flat-faithfully-flat-maximal-ideals`.
9. Apply `lem-weil-pbc-faithfully-flat-universally-injective` (Tag 05CK) to
`B / ∑ⱼ I b^j`. The relation of step 7 descends to `(b-1)b^d = ∑ⱼ iⱼ b^j` over `A`.
10. Set `f = X^d(X-1) - ∑ⱼ iⱼ X^j`. It is monic, annihilates `b`, and has the required
coefficients `aⱼ = -iⱼ ∈ I`. -/
theorem exists_monic_aeval_eq_zero_gabber_polynomial
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Finite A B] (I : Ideal A) (hI : I ≤ Ideal.jacobson ⊥)
    (B₁ : Type w) (B₂ : Type z) [CommRing B₁] [CommRing B₂]
    [Algebra (A ⧸ I) B₁] [Algebra (A ⧸ I) B₂]
    (e : (B ⧸ I.map (algebraMap A B)) ≃+* (B₁ × B₂))
    (he : ∀ a : A, e (Ideal.Quotient.mk (I.map (algebraMap A B)) (algebraMap A B a)) =
      (algebraMap (A ⧸ I) B₁ (Ideal.Quotient.mk I a),
        algebraMap (A ⧸ I) B₂ (Ideal.Quotient.mk I a)))
    (h₁ : Function.Surjective (algebraMap (A ⧸ I) B₁))
    (b : B) (hb : e (Ideal.Quotient.mk (I.map (algebraMap A B)) b) = (1, 0)) :
    ∃ (d : ℕ) (a : Fin (d + 1) → A) (f : A[X]),
      1 ≤ d ∧ (∀ j, a j ∈ I) ∧ f.Monic ∧ aeval b f = 0 ∧
        f = X ^ d * (X - 1) + ∑ j : Fin (d + 1), C (a j) * X ^ (j : ℕ) := by
  sorry

end Algebra
