/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Detecting non-pth-powers by absolute derivations

Source: Stacks Project, More on Algebra, Lemma 07PH (`lemma-find-D`)
(blueprint: lem-weil-pbc-derivation-nonzero-on-non-pth-power).
-/

set_option autoImplicit false

universe u v w

namespace Derivation

/-- Stacks Project, More on Algebra, Lemma 07PH (`lemma-find-D`).
(blueprint: lem-weil-pbc-derivation-nonzero-on-non-pth-power)
A non-pth-power in the fraction field of a characteristic-p domain of finite type over a
Noetherian complete local ring is detected by an absolute derivation of the domain.

Proof:
1. Replace the complete local base by its image in `B`, a complete Noetherian local domain
   by lem-weil-pbc-complete-local-quotient. By
   lem-weil-pbc-complete-local-domain-finite-over-regular it is finite over a power series
   ring over a field. The Cohen-ring alternative is excluded by characteristic `p`.
   Thus `B` is finite type over this power series ring.
2. By lem-weil-pbc-noether-normalization-over-domain, find a polynomial ring `A` over that
   base and `A ⊆ B' ⊆ B`, with `B'` finite over `A` and `B'_g = B_g` for nonzero `g`.
   The fraction field of `B'` is `M`. Choose `N` so that `f' = g^(p*N)*f` belongs to `B'`;
   it is still not a pth power, since a pth root would give one for `f` after division by
   `g^N`.
3. It suffices to find a derivation `D'` of `B'` nonzero on `f'`: by
   lem-weil-pbc-derivation-extends-finite-type-extension a multiple `g^r*D'` extends to `B`.
   Its value on `f'` is nonzero. The Leibniz rule and characteristic `p` imply
   `D(g^(p*N)) = 0`, so `D(f') = g^(p*N)*D(f)` and `D(f)` is nonzero.
4. The extension of fraction fields `M/K`, for `K = Frac(A)`, is finite, by integrality
   (lem-weil-pbc-finite-algebra-is-integral) and the finite module generators of `B'`.
   By lem-weil-pbc-differential-zero-iff-pth-power, `df'` is nonzero over the prime field.
   Choose a p-basis of the coefficient field (lem-weil-pbc-p-basis-exists). The subfields
   of lem-weil-pbc-power-series-ring-subfields and both parts of
   lem-weil-pbc-intersection-subfields-differentials give a finite-index coefficient
   subfield and `A' ⊆ A`, with `A` finite over `A'`, such that `df'` remains nonzero over
   a subfield containing `K' = Frac(A')`.
5. By lem-weil-pbc-vector-space-dual-separates, a linear functional on these differentials
   is nonzero on `df'`. The universal property of def-weil-pbc-kahler-differentials gives
   a derivation of `M` nonzero on `f'` and vanishing on `A'`.
6. By lem-weil-pbc-finite-module-over-finite-algebra, `B'` is finite over `A'`. Multiply
   the derivation by the product of denominators of its values on finitely many module
   generators. It then maps `B'` into `B'` and is still nonzero on `f'` because the
   product of denominators is nonzero in the domain. Step 3 completes the argument. -/
theorem exists_apply_ne_zero_of_not_pth_power
    (p : ℕ) [Fact p.Prime]
    (B : Type u) [CommRing B] [IsDomain B] [CharP B p]
    (M : Type v) [Field M] [Algebra B M] [IsFractionRing B M]
    (R₀ : Type w) [CommRing R₀] [IsNoetherianRing R₀] [IsLocalRing R₀]
    [IsAdicComplete (IsLocalRing.maximalIdeal R₀) R₀]
    [Algebra R₀ B] [Algebra.FiniteType R₀ B]
    (f : B) (hf : ¬ ∃ x : M, x ^ p = algebraMap B M f) :
    ∃ D : Derivation ℤ B B, D f ≠ 0 := by
  sorry

end Derivation
