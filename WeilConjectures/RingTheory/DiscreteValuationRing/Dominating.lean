/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.RingTheory.Valuation.LocalSubring
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Length

/-!
# Discrete valuation rings dominating noetherian local domains

Every noetherian local domain `O` which is not a field is dominated by a discrete valuation
ring: there is an injective local homomorphism from `O` to a discrete valuation ring
(Stacks `00PH`). In the one-dimensional case, every valuation ring of the fraction field of `O`
dominating `O` is discrete, by a length estimate in the spirit of the Krull–Akizuki theorem. The
general case reduces to the one-dimensional case by an affine blowup of the maximal ideal.

Geometrically, a specialisation `x' ⤳ x` of points of a locally noetherian scheme is the image of
the specialisation of the generic point to the closed point of the spectrum of a discrete
valuation ring (Stacks `054F`).

## Main statements

- `ValuationSubring.isDiscreteValuationRing_of_ringKrullDim_eq_one`: a valuation ring of the
  fraction field of a one-dimensional noetherian local domain `O` dominating `O` is discrete.
- `IsLocalRing.exists_isDiscreteValuationRing`: a noetherian local domain which is not a field is
  dominated by a discrete valuation ring.
- `Ideal.exists_isDiscreteValuationRing_of_lt`: for primes `p < q` of a noetherian ring `B` there
  is a homomorphism from `B` to a discrete valuation ring with kernel `p` under which the maximal
  ideal pulls back to `q`.

## References

- Stacks Project, Tags `00PH`, `054F`
-/

@[expose] public section

universe u

open IsLocalRing

/-- **Valuation rings dominating a one-dimensional noetherian local domain are discrete.** Let
`O` be a noetherian local domain of dimension one with fraction field `K`, and `V` a valuation
ring of `K` dominating `O`. Then `V` is a discrete valuation ring.

For `0 ≠ r ∈ O`, every strictly decreasing chain of ideals of `V` containing `r` has length at
most the length of `O ⧸ r O`: choosing elements witnessing the strict inclusions, they span a
finitely generated `O`-submodule `N` of `K` with `N ⧸ r N` of length that of `O ⧸ r O`. Hence
every nonzero ideal of `V` is principal. -/
theorem ValuationSubring.isDiscreteValuationRing_of_ringKrullDim_eq_one {O K : Type*}
    [CommRing O] [IsDomain O] [IsLocalRing O] [IsNoetherianRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] (hdim : ringKrullDim O = 1) (V : ValuationSubring K)
    (hV : ∀ x : O, algebraMap O K x ∈ V)
    (hloc : ∀ x ∈ maximalIdeal O, V.valuation (algebraMap O K x) < 1) :
    IsDiscreteValuationRing V := by
  sorry

/-- **Noetherian local domains are dominated by discrete valuation rings** (Stacks `00PH`). A
noetherian local domain `O` which is not a field admits an injective local homomorphism to a
discrete valuation ring. -/
theorem IsLocalRing.exists_isDiscreteValuationRing {O : Type u} [CommRing O] [IsDomain O]
    [IsLocalRing O] [IsNoetherianRing O] (hO : ¬IsField O) :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R)
      (f : O →+* R), Function.Injective f ∧ IsLocalHom f := by
  sorry

/-- **Specialisations are traced by discrete valuation rings** (Stacks `054F`). For primes
`p < q` of a noetherian ring `B` there is a homomorphism `φ` from `B` to a discrete valuation
ring with kernel `p` such that the maximal ideal pulls back to `q`. -/
theorem Ideal.exists_isDiscreteValuationRing_of_lt {B : Type u} [CommRing B] [IsNoetherianRing B]
    {p q : Ideal B} [p.IsPrime] [q.IsPrime] (hpq : p < q) :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R)
      (φ : B →+* R), RingHom.ker φ = p ∧ (maximalIdeal R).comap φ = q := by
  sorry
