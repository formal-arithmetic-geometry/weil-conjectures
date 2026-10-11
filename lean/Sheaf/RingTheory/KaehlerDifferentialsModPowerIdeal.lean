/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Kähler differentials modulo a power of an ideal

Source: Stacks Project, Algebra, Lemma Tag 02HQ (`lemma-differential-mod-power-ideal`),
with the conormal sequence of Tag 00RU
(blueprint: lem-weil-pbc-kahler-differentials-mod-power-ideal).

The quotient factor is written first in the tensor products, using tensor symmetry,
so that Mathlib supplies the canonical quotient-ring module structures.
-/

@[expose] public section

universe u v

open scoped TensorProduct

/-- For `S' = S/I^(n+1)`, reduction modulo `I^n` identifies the relative
Kähler differentials of `S` and `S'` after tensoring with `S/I^n`.
The generator formula specifies the induced map, with tensor factors interchanged.

Source: Stacks Project, Algebra, Lemma Tag 02HQ
(blueprint: lem-weil-pbc-kahler-differentials-mod-power-ideal).

Proof:
1. Apply the conormal exact sequence of Tag 00RU to `S → S'`, with kernel `I^(n+1)`
   (`lem-weil-pbc-jacobi-zariski-differential-maps`). Tensor it over `S'` with `S/I^n`;
   tensor right exactness (`lem-weil-pbc-tensor-right-exact`) preserves exactness
   and surjectivity of the map to the differentials of `S'`.
2. Cancel base change (`lem-weil-pbc-module-tensor-cancel-base-change`) and use
   tensor symmetry to identify the middle term with `S/I^n ⊗[S] Ω[S/R]`.
   The map sends `t ⊗ ds` to `t ⊗ d(s mod I^(n+1))`, and its kernel is generated
   by `t ⊗ da` for `a ∈ I^(n+1)`.
3. The iterated Leibniz rule (`def-weil-pbc-kahler-differentials`) gives
   `d(a₀⋯aₙ) = ∑ᵢ (∏ⱼ≠ᵢ aⱼ) daᵢ`. For `aⱼ ∈ I`, each coefficient belongs
   to `I^n`. Additivity extends this to `d(I^(n+1)) ⊆ I^n Ω[S/R]`.
4. Each kernel generator is zero: move its coefficients in `I^n` to the quotient
   factor, where they vanish. Thus the induced map is injective and surjective,
   hence an isomorphism of `S/I^n`-modules. -/
theorem kahlerDifferential_mod_power_ideal
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal S) (n : ℕ) (_hn : 1 ≤ n) :
    letI : Algebra (S ⧸ I ^ (n + 1)) (S ⧸ I ^ n) :=
      (Ideal.Quotient.factorPowSucc I n).toAlgebra
    ∃ e : (S ⧸ I ^ n) ⊗[S] KaehlerDifferential R S ≃ₗ[S ⧸ I ^ n]
        (S ⧸ I ^ n) ⊗[S ⧸ I ^ (n + 1)] KaehlerDifferential R (S ⧸ I ^ (n + 1)),
      ∀ (s : S) (t : S),
        e (Ideal.Quotient.mk (I ^ n) t ⊗ₜ[S] KaehlerDifferential.D R S s) =
          Ideal.Quotient.mk (I ^ n) t ⊗ₜ[S ⧸ I ^ (n + 1)]
            KaehlerDifferential.D R (S ⧸ I ^ (n + 1))
              (Ideal.Quotient.mk (I ^ (n + 1)) s) := by
  sorry
