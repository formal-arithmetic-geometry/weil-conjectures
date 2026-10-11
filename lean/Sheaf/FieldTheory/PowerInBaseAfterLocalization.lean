/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Powers in the base after localization

Source: literature/stacks-project/algebra.tex, Algebra, Section 0BR5
(section-universal-homeomorphism), denominator-clearing input to Lemma 0BR8
(lemma-powers) for a finite purely inseparable extension
(blueprint: lem-weil-pbc-power-in-base-after-localization).
-/

set_option autoImplicit false

universe u v w z

open scoped TensorProduct

namespace RingTheory

/--
Source: literature/stacks-project/algebra.tex, Algebra, Section 0BR5
(section-universal-homeomorphism), denominator-clearing input to Lemma 0BR8
(lemma-powers) for a finite purely inseparable extension.

Proof, following the node's steps:
1. By `def-weil-finite-integral-morphism`, choose finitely many module generators
   e_i of E. The compatible fraction-field maps embed A' and E into L.
   By `def-pc-field-extension` and `def-weil-pbc-finite-purely-inseparable-extension`,
   each generator lies in K' in characteristic zero, and a common p^N-th power
   of all generators lies in K' in characteristic p. Write these elements as
   b_i/t_i, with nonzero t_i in A', and take s to be the product of the t_i.
   Localization embeds A'[1/s] in K' and E[1/s] in L; the displayed generators
   or their common powers then belong to the localized base.
2. In characteristic zero, E[1/s] is spanned by generators in A'[1/s], so the
   canonical inclusion of the base is surjective. It is injective by step 1,
   and hence this says E[1/s] = A'[1/s] as subrings of L.
3. In characteristic p, write any x as a finite A'[1/s]-linear combination of
   the e_i. Frobenius to the common power p^N distributes over this sum, and
   each summand is in the base. Thus x^(p^N) is in the base, allowing n = N.
4. Since s is nonzero and the maps are compatible, localization preserves
   the fraction fields K' and L. This establishes both characteristic clauses.
(blueprint: lem-weil-pbc-power-in-base-after-localization)
-/
theorem power_in_base_after_localization
    (A' : Type u) (K' : Type v) (E : Type w) (L : Type z)
    [CommRing A'] [IsDomain A'] [IsNoetherianRing A']
    [Field K'] [Field L]
    [CommRing E] [IsDomain E]
    [Algebra A' E] [Module.Finite A' E]
    [Algebra A' K'] [Algebra E L] [Algebra K' L] [Algebra A' L]
    [IsScalarTower A' E L] [IsScalarTower A' K' L]
    [Module.Finite K' L] [IsPurelyInseparable K' L]
    [IsFractionRing A' K'] [IsFractionRing E L] :
    ∃ s : A', s ≠ 0 ∧
      (CharZero K' → Function.Surjective
        (Algebra.TensorProduct.includeRight (R := A') (A := E)
          (B := Localization.Away s) :
          Localization.Away s → E ⊗[A'] Localization.Away s)) ∧
      (∀ p : ℕ, Nat.Prime p → CharP K' p →
        ∀ x : E ⊗[A'] Localization.Away s, ∃ n : ℕ, ∃ a : Localization.Away s,
          Algebra.TensorProduct.includeRight (R := A') (A := E)
            (B := Localization.Away s) a = x ^ (p ^ n)) := by
  sorry

end RingTheory
