module

public import Mathlib.RingTheory.AdicCompletion.Algebra

/-!
# Compatible isomorphisms of adic quotients

Source: literature/stacks-project/algebra.tex, Tag 00M9 (section-completion),
compatible finite-level maps and the inverse-limit description of completion
(blueprint: lem-trf-adic-inverse-limit-iso).
-/

@[expose] public section

universe u v


/-- Compatible isomorphisms of positive adic quotients induce a unique isomorphism of
adic completions.  This is the inverse-limit construction from Stacks Project,
Tag 00M9 (section-completion):

1. Using [def-weil-pbc-adic-completion], regard both completions as compatible
   tuples.  Define the map coordinatewise by `e n`; compatibility with the
   quotient transitions makes the result a tuple, and componentwise operations
   make it a ring homomorphism with the displayed projection identities.
2. The inverse quotient isomorphisms satisfy the reversed transition identities,
   so they define the inverse compatible-tuple map.  Coordinatewise cancellation
   gives both composites as identities, hence a ring isomorphism.
3. Any map with the same projection identities has equal coordinates to the
   constructed map, so equality of tuples gives uniqueness even among maps of
   sets.

(blueprint: lem-trf-adic-inverse-limit-iso)
-/
theorem adicCompletionRingEquivOfCompatible
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (I : Ideal A) (J : Ideal B)
    (e : ∀ n : ℕ, 0 < n → (A ⧸ I ^ n) ≃+* (B ⧸ J ^ n))
    (he : ∀ {m n : ℕ} (hmn : m ≤ n) (hm : 0 < m) (hn : 0 < n),
      (Ideal.Quotient.factorPow J hmn).comp (e n hn).toRingHom =
        (e m hm).toRingHom.comp (Ideal.Quotient.factorPow I hmn)) :
    ∃ E : AdicCompletion I A ≃+* AdicCompletion J B,
      (∀ (n : ℕ) (hn : 0 < n) (x : AdicCompletion I A),
        AdicCompletion.evalₐ J n (E x) =
          e n hn (AdicCompletion.evalₐ I n x)) ∧
      (∀ F : AdicCompletion I A → AdicCompletion J B,
        (∀ (n : ℕ) (hn : 0 < n) (x : AdicCompletion I A),
          AdicCompletion.evalₐ J n (F x) =
            e n hn (AdicCompletion.evalₐ I n x)) →
        F = E.toFun) := by
  sorry

end
