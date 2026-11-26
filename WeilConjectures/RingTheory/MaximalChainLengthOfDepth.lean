/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.Depth
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Order.Preorder.Chain
public import Mathlib.Order.RelSeries
import Mathlib.Order.KrullDimension
import WeilConjectures.RingTheory.MaximalChainLengthOfDepthPositive

/-!
# Length of maximal prime chains in a Cohen–Macaulay local ring

In a Noetherian local ring of dimension `d` and depth at least `d` (a Cohen–Macaulay local
ring), every maximal chain of primes has length `d`.

## Implementation details

The proof is by induction on `d`. For `d > 0` the chain has positive length. Prime avoidance
gives `x` in the second prime outside all minimal primes, and some power `y = x^k` makes the
second prime associated to `S/yS`. Then `y` is regular and `S/yS` is Noetherian local of
dimension `d - 1` and depth at least `d - 1`; the image of the second prime is associated,
hence minimal, so the images of the remaining primes form a maximal chain in `S/yS`.

## References

* [Stacks, Tag 00N9]
* [Stacks, Tag 0AAE] (for the module `S`)
-/

@[expose] public section

universe u

namespace IsLocalRing

/-- Every maximal chain of primes in a Noetherian local ring of dimension `d` and depth
at least `d` has length `d`.

The chain is an `LTSeries` `p` of primes (as `ringKrullDim` is built), with `n = p.length`
strict inclusions among its `n + 1` entries `p 0 < ⋯ < p n`. Maximality of its range means
that no prime can be inserted before, between, or after its entries. The depth here
is the depth of `S` as a module over itself, with respect to its maximal ideal, using
`RingTheory.Sequence.IsRegular`. -/
theorem maximal_chain_length_eq_of_depth {S : Type u} [CommRing S]
    [IsNoetherianRing S] [IsLocalRing S] (d : ℕ)
    (hdim : ringKrullDim S = (d : WithBot ℕ∞))
    (hdepth : (d : ℕ∞) ≤ IsLocalRing.depth (R := S) S) (p : LTSeries (PrimeSpectrum S))
    (hmax : IsMaxChain (fun q r : PrimeSpectrum S ↦ q ≤ r) (Set.range p)) :
    p.length = d := by
  induction d generalizing S with
  | zero =>
    have hp : p.length ≤ 0 := by
      have hle := Order.LTSeries.length_le_krullDim p
      change (p.length : WithBot ℕ∞) ≤ ringKrullDim S at hle
      rw [hdim] at hle
      exact_mod_cast hle
    exact Nat.eq_zero_of_le_zero hp
  | succ d ih =>
    exact maximal_chain_length_eq_of_depth_pos d ih hdim hdepth p hmax

end IsLocalRing
