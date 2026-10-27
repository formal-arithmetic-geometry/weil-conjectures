module

public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Fraction fields under an injective map with unit denominators

Source: ILO VIII, Lemmas 3.2.9 and 3.2.12, printed p.104; Stacks Tags 09FJ and 00CO
(blueprint: lem-trf-unit-denominator-fraction-equivalence).
-/

@[expose] public section

universe u v

namespace RingHom

/-- An injective map with unit denominators has a domain as target and induces an
isomorphism of fraction fields, with the indicated formulas.

Source: ILO VIII, Lemma 3.2.9 proof and Lemma 3.2.12 first proof paragraph, printed p.104;
the explicit algebra is the fraction construction of Stacks Tags 09FJ and 00CO
(blueprint: lem-trf-unit-denominator-fraction-equivalence).

Proof:
1. Injectivity sends the distinct elements 0 and 1 of A to distinct elements of B.
   A unit in B cannot be zero, so every unit denominator has nonzero preimage in A.
2. Given x*y = 0, choose unit denominators with i(s)*x = i(a) and i(t)*y = i(b).
   Then i(a*b) = 0; injectivity and the domain property give a = 0 or b = 0.
   Cancel the corresponding unit to get x = 0 or y = 0. Thus B is a domain.
3. Write k for the injection B → Frac(B), supplied by the fraction construction.
   Define J(a/s) = k(i(a))/k(i(s)). Cross multiplication and injectivity make this
   well defined; the usual fraction sum and product formulas make it a unital ring map.
   Taking s = 1 shows that it extends i.
4. Equality of two images gives i(a)*i(t) = i(b)*i(s). Injectivity gives a*t = b*s,
   so cross multiplication in Frac(A) proves that J is injective.
5. For x/y with y nonzero choose the stated presentations. The unit denominators
   give s,t nonzero, and i(t)*y = i(b) gives b nonzero. Thus s*b is nonzero.
   The fraction calculation gives J((t*a)/(s*b)) = x/y. Every fraction has such
   a presentation, proving both the last formula and surjectivity.
6. The bijective ring map is a ring isomorphism; its inverse preserves the ring
   operations by applying J and using injectivity. Step 3 gives the extension clause.
-/
theorem exists_fractionRing_equiv_of_unit_denominators
    {A : Type u} {B : Type v} [CommRing A] [IsDomain A] [CommRing B]
    (i : A →+* B) (hi : Function.Injective i)
    (hden : ∀ x : B, ∃ a s : A, IsUnit (i s) ∧ i s * x = i a) :
    ∃ (_ : IsDomain B) (J : FractionRing A ≃+* FractionRing B),
      (∀ a s : A, s ≠ 0 →
        J (algebraMap A (FractionRing A) a / algebraMap A (FractionRing A) s) =
          algebraMap B (FractionRing B) (i a) / algebraMap B (FractionRing B) (i s)) ∧
      (∀ a : A, J (algebraMap A (FractionRing A) a) =
        algebraMap B (FractionRing B) (i a)) ∧
      (∀ (x y : B) (a s b t : A), y ≠ 0 → IsUnit (i s) → IsUnit (i t) →
        i s * x = i a → i t * y = i b →
        s * b ≠ 0 ∧
          J (algebraMap A (FractionRing A) (t * a) /
              algebraMap A (FractionRing A) (s * b)) =
            algebraMap B (FractionRing B) x / algebraMap B (FractionRing B) y) := by
  sorry

end RingHom
