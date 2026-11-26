/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import WeilConjectures.RingTheory.GRingPairsForward
import WeilConjectures.RingTheory.GRingPairsBackward

/-!
# The G-ring criterion using pairs of prime ideals

A Noetherian ring `R` is a G-ring exactly when, for all primes `q ≤ p`, the generic formal
fibre of the local ring of `R/q` at `p/q` is Noetherian and geometrically regular.

## Implementation details

Here `p.map (Ideal.Quotient.mk q)` is `p/q` in `B = R/q`, and the residue field
`q.ResidueField` is the fraction field of `B` with its canonical `B`-algebra structure. We use
the residue-field-first tensor order, canonically isomorphic to the order in the source.

The proof identifies the fibre with `κ(q) ⊗[R] completion(R_p)`, using the surjection
`R_p → (R/q)_(p/q)` and the completion of a quotient; this ring is zero when `q ⊈ p`. Since
`R → completion(R_p)` is flat, regularity of the local completion maps is equivalent to the
fibre condition for all `q ≤ p`.

## References

* [Stacks, Tag 07PN]
* [Stacks, Tag 07GH]
-/

@[expose] public section

universe u

/-- A Noetherian ring is a G-ring exactly when the generic formal fibres of all its
prime quotients, localized at primes containing the quotient ideal, are Noetherian and
geometrically regular. -/
theorem isGRing_iff_pairsOfPrimes (R : Type u) [CommRing R] [IsNoetherianRing R] :
    IsGRing R ↔ ∀ (q p : Ideal R) [q.IsPrime] [p.IsPrime] (hqp : q ≤ p),
      let pbar := p.map (Ideal.Quotient.mk q)
      letI : pbar.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hqp
      let L := Localization.AtPrime pbar
      let C := AdicCompletion (IsLocalRing.maximalIdeal L) L
      let F := TensorProduct (R ⧸ q) q.ResidueField C
      IsNoetherianRing F ∧ Algebra.IsGeometricallyRegular q.ResidueField F := by
  exact ⟨isGRing_pairsOfPrimes_forward R, isGRing_pairsOfPrimes_backward R⟩
