module

public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.Order.Preorder.Chain
public import Mathlib.Order.RelSeries
public import Sheaf.RingTheory.Depth

import Sheaf.RingTheory.AssociatedPrimeMinimalOfDepth
import Sheaf.RingTheory.AssociatedPrimePowerQuotient
import Sheaf.RingTheory.DepthQuotientNonzerodivisor
import Sheaf.RingTheory.IsRegularOfDimensionDrop
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import Mathlib.RingTheory.KrullDimension.Regular

/-! Positive-dimensional induction step for maximal Cohen--Macaulay prime chains.
Source: Stacks Project, Algebra, Lemma 10.104.3 (Tag 00N9), via 10.103.9
(blueprint: lem-weil-pbc-cm-local-maximal-chain-length-positive). -/

@[expose] public section

universe u

namespace IsLocalRing

/-- The successor step for the maximal-chain theorem, assuming its dimension-`d` case.
Source: Stacks Project, Algebra, Tag 00N9, proof via Tag 0AAE.
(blueprint: lem-weil-pbc-cm-local-maximal-chain-length-positive)

Proof: Maximality makes the first prime minimal, the last prime maximal, and every
adjacent pair saturated. The chain has positive length: otherwise the maximal ideal
is minimal, so every prime equals it and the ring has dimension zero, contradicting
its dimension `d + 1`. The finitely many minimal primes contain none of the second
prime, since the first prime lies strictly below it. Prime avoidance therefore gives
`x` in the second prime outside all minimal primes. The first prime is associated
in the Noetherian ring, and the second prime is minimal over the first plus `(x)`
by saturation and `x` not belonging to the first prime. The associated-prime power
quotient theorem gives a positive power `y` of `x` for which the second prime is
associated to `S/yS`. This power still avoids every minimal prime and belongs to
the maximal ideal. Dimension drop gives `dim(S/yS) = d`; the dimension-drop
regularity theorem makes `y` a nonzerodivisor, and the quotient depth theorem gives
depth at least `d` in this Noetherian local quotient. The associated element has
annihilator over the quotient equal to the image of the second prime, so associated
prime minimality makes that image minimal. Prime correspondence maps the tail of
the original chain to a strict chain in the quotient, of length `p.length - 1`.
It is maximal: its first prime is minimal, its last prime is the maximal ideal,
and saturation is preserved and reflected by prime correspondence. Apply `ih`
to this quotient chain to obtain `p.length - 1 = d`. The positive length of `p`
then gives `p.length = d + 1`. -/
theorem maximal_chain_length_eq_of_depth_pos {S : Type u} [CommRing S]
    [IsNoetherianRing S] [IsLocalRing S] (d : ℕ)
    (ih : ∀ {T : Type u} [CommRing T] [IsNoetherianRing T] [IsLocalRing T],
      ringKrullDim T = (d : WithBot ℕ∞) →
      (d : ℕ∞) ≤ IsLocalRing.depth (R := T) T →
      ∀ q : LTSeries (PrimeSpectrum T),
        IsMaxChain (fun a b : PrimeSpectrum T ↦ a ≤ b) (Set.range q) → q.length = d)
    (hdim : ringKrullDim S = ((d + 1 : ℕ) : WithBot ℕ∞))
    (hdepth : ((d + 1 : ℕ) : ℕ∞) ≤ IsLocalRing.depth (R := S) S)
    (p : LTSeries (PrimeSpectrum S))
    (hmax : IsMaxChain (fun q r : PrimeSpectrum S ↦ q ≤ r) (Set.range p)) :
    p.length = d + 1 := by
  sorry

end IsLocalRing
