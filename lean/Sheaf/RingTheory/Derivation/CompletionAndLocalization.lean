/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Localization.Basic

/-!
# Extension of derivations to completions and localizations

Source: Stacks Project, More on Algebra, Lemma 07PE, parts (1) and (2)
(blueprint: lem-weil-pbc-derivation-extends).
-/

universe u

namespace Derivation

/-- Stacks Project, More on Algebra, Lemma 07PE, parts (1) and (2)
(blueprint: lem-weil-pbc-derivation-extends). An absolute derivation extends to every adic
completion by the maps between successive quotients, and uniquely to every localization
by the quotient rule. Absolute derivations are represented as derivations over `ℤ`.

Proof, following the node's eleven steps:
1. The Leibniz rule at `1 * 1` gives `D 1 = 0`.
2. Induction and the Leibniz rule on products generating `I ^ (n + 1)` give
   `D (I ^ (n + 1)) ⊆ I ^ n`.
3. Hence `D` induces additive maps `d n : R / I ^ (n + 1) → R / I ^ n`.
   Their Leibniz rule uses the reduction map, and they commute with reductions.
4. On compatible sequences set the n-th component of `Dc x` to `d n (x (n + 1))`.
   The preceding compatibility makes this a compatible sequence
   [def-weil-pbc-adic-completion].
5. Additivity and the Leibniz rule hold componentwise, since the reductions of
   `x (n + 1)` and `y (n + 1)` are `x n` and `y n`.
6. On the canonical image of `a`, each component is `D a mod I ^ n`, so `Dc` extends `D`.
7. Any localization extension is forced by differentiating `w * (1 / w) = 1`:
   its value at `a / w` is `D a / w - a * D w / w ^ 2`.
8. This formula is well defined. If `u * z = 0`, where `z = a * w' - a' * w`,
   differentiating and multiplying by `u` gives `u ^ 2 * D z = 0`.
   The difference of the two quotient-rule numerators is
   `w * w' * D z - z * D (w * w')`, which is killed by `u ^ 2`.
9. Expanding the numerator for `(a * v + b * w) / (w * v)` gives additivity.
10. Expanding the numerator for `a * b / (w * v)` gives the Leibniz rule.
11. At `a / 1` the formula gives `D a / 1`, since `D 1 = 0`, so it extends `D`.
-/
theorem exists_completion_and_unique_localization (R : Type u) [CommRing R]
    (D : Derivation ℤ R R) :
    (∀ I : Ideal R,
      ∃ Dc : Derivation ℤ (AdicCompletion I R) (AdicCompletion I R),
        ∃ d : (n : ℕ) → (R ⧸ I ^ (n + 1)) →+ (R ⧸ I ^ n),
          (∀ a : R, Dc (algebraMap R (AdicCompletion I R) a) =
            algebraMap R (AdicCompletion I R) (D a)) ∧
          (∀ (n : ℕ), 1 ≤ n → ∀ a : R,
            d n (Ideal.Quotient.mk (I ^ (n + 1)) a) = Ideal.Quotient.mk (I ^ n) (D a)) ∧
          (∀ (n : ℕ), 1 ≤ n → ∀ x : AdicCompletion I R,
            AdicCompletion.evalₐ I n (Dc x) = d n (AdicCompletion.evalₐ I (n + 1) x))) ∧
    (∀ W : Submonoid R,
      ∃ Dw : Derivation ℤ (Localization W) (Localization W),
        (∀ a : R, Dw (algebraMap R (Localization W) a) =
          algebraMap R (Localization W) (D a)) ∧
        (∀ (a : R) (w : W), Dw (Localization.mk a w) =
          Localization.mk (D a) w - Localization.mk (a * D (w : R)) (w ^ 2)) ∧
        (∀ Dw' : Derivation ℤ (Localization W) (Localization W),
          (∀ a : R, Dw' (algebraMap R (Localization W) a) =
            algebraMap R (Localization W) (D a)) → Dw' = Dw)) := by
  sorry

end Derivation
