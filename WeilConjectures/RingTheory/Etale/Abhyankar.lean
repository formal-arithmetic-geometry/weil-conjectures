/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Invariant.Basic

/-!
# Abhyankar's lemma for Galois algebras over a discrete valuation ring

Let `O` be a discrete valuation ring with uniformizer `π` and fraction field `F`, and let `L` be
a finite étale `F`-algebra with an action of a finite group `G` by `F`-algebra automorphisms
such that `L` is Galois with group `G` (`[L : F] = |G|` and `L^G = F`). Assume `|G|` divides an
integer `n` invertible in `O`. Then the extension is tamely ramified, and after adjoining an
`n`-th root `t` of `π` it becomes unramified: the integral closure of `O₂ = O[t]/(tⁿ - π)` in
`O₂ ⊗_O L` is finite étale over `O₂`
(`IsDiscreteValuationRing.etale_integralClosure_adjoinRoot`).

This is Abhyankar's lemma ([Stacks 0EYG], [Stacks 09E8] for the tameness), an input of the trait
case of blueprint `sbc-thm-spreading-finite-etale-galois` ([Stacks 0EYJ]).
-/

@[expose] public section

universe u

open Polynomial TensorProduct

namespace IsDiscreteValuationRing

variable {O F L : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F]
  [Algebra O F] [IsFractionRing O F] [CommRing L] [Algebra F L] [Algebra O L]
  [IsScalarTower O F L] [Algebra.Etale F L]

/-- **Abhyankar's lemma** for Galois algebras over a discrete valuation ring. See the module
docstring. -/
theorem etale_integralClosure_adjoinRoot (G : Type*) [Group G] [Finite G]
    [MulSemiringAction G L] [SMulCommClass G F L]
    (hrank : Module.finrank F L = Nat.card G)
    (hfix : ∀ x : L, (∀ g : G, g • x = x) → x ∈ Set.range (algebraMap F L))
    {n : ℕ} (hGn : Nat.card G ∣ n) (hn : IsUnit (n : O)) {π : O} (hπ : Irreducible π) :
    Algebra.Etale (AdjoinRoot (X ^ n - C π))
        (integralClosure (AdjoinRoot (X ^ n - C π)) (AdjoinRoot (X ^ n - C π) ⊗[O] L)) ∧
      Module.Finite (AdjoinRoot (X ^ n - C π))
        (integralClosure (AdjoinRoot (X ^ n - C π)) (AdjoinRoot (X ^ n - C π) ⊗[O] L)) := by
  sorry

end IsDiscreteValuationRing
