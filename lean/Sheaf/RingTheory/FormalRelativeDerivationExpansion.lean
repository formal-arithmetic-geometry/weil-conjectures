/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.RingTheory.MvPowerSeries.Trunc
import WeilConjectures.RingTheory.PowerSeriesCombinedIdealCoefficients

/-!
# Adic expansion of relative derivations of formal power series

Source: literature/stacks-project/curves.tex, Tag 0C4B
(lemma-fitting-ideal-well-defined), final coordinate-change paragraph; the explicit
adic argument supplies its omitted chain-rule details.
(blueprint: lem-trf-formal-relative-derivation-expansion)
-/

@[expose] public section

universe u

namespace MvPowerSeries

/-- A relative derivation along a local homomorphism of finite-variable formal power
series algebras lowers the variable-ideal filtration by one. Total-degree polynomial
truncations have the four stated tail estimates and satisfy the finite Leibniz formula;
separatedness then gives the exact expansion by formal partial derivatives.

Source: literature/stacks-project/curves.tex, Tag 0C4B
(lemma-fitting-ideal-well-defined), final coordinate-change paragraph, where the
chain-rule details are omitted.
(blueprint: lem-trf-formal-relative-derivation-expansion)

Proof:
1. Specialize `power_series_mem_combined_ideal_pow_iff`
   (lem-weil-pbc-power-series-combined-ideal-coefficients) to base ideal zero, with
   respectively m and r variables. A series lies in the Nth variable-ideal power
   exactly when its coefficients of total degree below N vanish. There are finitely
   many such multi-indices. The coefficient formula for `truncTotal` therefore puts
   h minus its truncation in that power. A series in every target power has its
   coefficient at beta zero by using N = degree beta + 1, proving separatedness.
2. The relative Leibniz rule at 1 gives E(1) = 0, so F-linearity makes E vanish on
   constants. Products of N elements of the source variable ideal have images under
   psi in the Nth target power. The iterated Leibniz rule expresses E of such a
   product as a sum with N-1 image factors in every term. Finite sums prove the
   order-lowering bound and its application to the truncation tail.
3. The coefficient formula of `pderiv`
   (def-trf-formal-power-series-partial-derivative) shows that differentiating a
   tail vanishing below degree N produces a tail vanishing below degree N-1.
   For N = 1 this is membership in the zeroth ideal power. Apply the coefficient
   criterion and the inclusion of ideal powers under psi for the other tail bounds.
4. Induct on monomial degree with the relative Leibniz rule: E of a monomial is the
   sum over variables of its formal partial derivative mapped by psi times E of that
   variable. The degree-zero case is E(1) = 0. Multiply by the coefficient in F and
   sum over the finite truncation. F-linearity and psi fixing F give its formula.
5. Subtract this polynomial formula from the desired full-series formula. Additivity
   writes the difference as E of the tail minus the sum of mapped tail derivatives
   times E of the variables. All terms lie in the (N-1)st target power. Set N = k+1
   for every k and use separatedness to obtain equality. If m = 0, all series are
   constant and E and the empty sum vanish. If r = 0, the target variable ideal is
   zero; the same bounds apply. No integer is inverted, so all characteristics occur.
-/
theorem formal_relative_derivation_expansion
    (F : Type u) [Field F] (m r : ℕ)
    (ψ : MvPowerSeries (Fin m) F →ₐ[F] MvPowerSeries (Fin r) F)
    (E : MvPowerSeries (Fin m) F →ₗ[F] MvPowerSeries (Fin r) F)
    (hψ : ∀ f : MvPowerSeries (Fin m) F,
      f ∈ Ideal.span (Set.range (X : Fin m → MvPowerSeries (Fin m) F)) →
      ψ f ∈ Ideal.span (Set.range (X : Fin r → MvPowerSeries (Fin r) F)))
    (hE : ∀ f g : MvPowerSeries (Fin m) F,
      E (f * g) = ψ f * E g + ψ g * E f) :
    (∀ N : ℕ, 1 ≤ N → ∀ f : MvPowerSeries (Fin m) F,
      f ∈ (Ideal.span (Set.range (X : Fin m → MvPowerSeries (Fin m) F))) ^ N →
      E f ∈ (Ideal.span (Set.range (X : Fin r → MvPowerSeries (Fin r) F))) ^ (N - 1)) ∧
    (∀ (h : MvPowerSeries (Fin m) F) (N : ℕ), 1 ≤ N →
      (h - (truncTotal N h : MvPowerSeries (Fin m) F) ∈
        (Ideal.span (Set.range (X : Fin m → MvPowerSeries (Fin m) F))) ^ N) ∧
      (∀ j : Fin m, pderiv F j (h - (truncTotal N h : MvPowerSeries (Fin m) F)) ∈
        (Ideal.span (Set.range (X : Fin m → MvPowerSeries (Fin m) F))) ^ (N - 1)) ∧
      (E (h - (truncTotal N h : MvPowerSeries (Fin m) F)) ∈
        (Ideal.span (Set.range (X : Fin r → MvPowerSeries (Fin r) F))) ^ (N - 1)) ∧
      (∀ j : Fin m, ψ (pderiv F j (h - (truncTotal N h : MvPowerSeries (Fin m) F))) ∈
        (Ideal.span (Set.range (X : Fin r → MvPowerSeries (Fin r) F))) ^ (N - 1)) ∧
      (E (truncTotal N h : MvPowerSeries (Fin m) F) =
        ∑ j : Fin m, ψ (pderiv F j (truncTotal N h : MvPowerSeries (Fin m) F)) * E (X j)) ∧
      (E h - ∑ j : Fin m, ψ (pderiv F j h) * E (X j) ∈
        (Ideal.span (Set.range (X : Fin r → MvPowerSeries (Fin r) F))) ^ (N - 1))) ∧
    (⨅ N : ℕ,
      (Ideal.span (Set.range (X : Fin r → MvPowerSeries (Fin r) F))) ^ N) = ⊥ ∧
    (∀ h : MvPowerSeries (Fin m) F,
      E h = ∑ j : Fin m, ψ (pderiv F j h) * E (X j)) := by
  sorry

end MvPowerSeries
