/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.Order.Preorder.Chain
public import Mathlib.Order.RelSeries
import WeilConjectures.RingTheory.FiniteTypeDomainDimensionLocalRingLocalization
import WeilConjectures.RingTheory.FiniteTypeDomainDimensionLocalRingChains

/-!
# Dimension of local rings of finite type domains over fields

A domain `S` of finite type over a field has the same dimension as each of its localizations at
maximal ideals, and all maximal chains of primes in `S` have this common finite length.

## Implementation details

The proof presents `S` as `k[x₁, ..., xₙ] / a` with `a` prime and shows `dim S = n - ht a` by
comparing saturated chains with chains in the polynomial ring. The two halves of the statement
are proved in `FiniteTypeDomainDimensionLocalRingLocalization` and
`FiniteTypeDomainDimensionLocalRingChains`. `LTSeries` counts strict inclusions, and `IsMaxChain`
of its range means that no prime can be inserted before, between, or after its entries.

## References

* [Stacks, Tag 00OS]
-/

@[expose] public section

universe u v

/-- A finite type domain over a field has the dimension of each of its local rings at
maximal ideals, and all maximal prime chains have this common finite length. -/
theorem finiteTypeDomain_ringKrullDim_localizationAtMaximal
    {k : Type u} [Field k] {S : Type v} [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] [IsDomain S] :
    (∀ (m : Ideal S) [m.IsMaximal],
      ringKrullDim (Localization.AtPrime m) = ringKrullDim S) ∧
    (∃ (d : ℕ), ringKrullDim S = (d : WithBot ℕ∞) ∧
      ∀ (p : LTSeries (PrimeSpectrum S)),
        IsMaxChain (fun q r : PrimeSpectrum S ↦ q ≤ r) (Set.range p) →
          p.length = d) := by
  exact ⟨finiteTypeDomain_ringKrullDim_localizationAtMaximal_localization (k := k) (S := S),
    finiteTypeDomain_ringKrullDim_localizationAtMaximal_chains (k := k) (S := S)⟩
