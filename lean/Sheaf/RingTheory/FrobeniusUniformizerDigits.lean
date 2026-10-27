module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharP.Basic
import WeilConjectures.Mathlib.Algebra.CharP.Lemmas

/-!
# Frobenius digits after adjoining a uniformizer radical

Source: Stacks Project, More on Algebra, Tag 09EY, `lemma-purely-inseparable-case`,
last two proof paragraphs, in the complete-ring form with the specified root ring `S`
(blueprint: lem-sfb-epp-frobenius-uniformizer-digits).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace IsDiscreteValuationRing

/-- Over an injective local map of complete DVRs of characteristic `p`, with `s ^ p = f t`,
each element has either a finite Frobenius digit expansion ending in a nonpower residue,
or a `p`th root in `S`.

Source: Stacks Project, More on Algebra, Tag 09EY, `lemma-purely-inseparable-case`,
last two proof paragraphs, in the complete-ring form with the specified root ring `S`
(blueprint: lem-sfb-epp-frobenius-uniformizer-digits).

Proof: If a finite expansion ending in a nonpower residue exists, take that alternative.
Otherwise start with `r₀ = x` and maintain
`x = ∑ i < n, bᵢ ^ p * t ^ i + rₙ * t ^ n`. The residue of `rₙ` is a `p`th power,
since otherwise this identity is the first alternative. Lift a residue root to `bₙ` in `R`.
The quotient map has kernel `(t)`, so choose `rₙ₊₁` with `rₙ = bₙ ^ p + t * rₙ₊₁`.
This gives the identity at the next stage, and recursive choice supplies all the digits.
In `S`, the partial sums `wₙ = ∑ i < n, f bᵢ * s ^ i` are compatible modulo `(s ^ n)`:
every later difference is divisible by `s ^ n`. As `s` generates the maximal ideal,
adic completeness supplies `w` with `w - wₙ` in `(s ^ n)` for every `n`.
Frobenius is additive and multiplicative in characteristic `p`
(`def-weil-ring-frobenius`), hence `wₙ ^ p` is the image of the finite digit sum and
`w ^ p - wₙ ^ p = (w - wₙ) ^ p` lies in `(s ^ (p * n))`.
The maintained identity and `s ^ p = f t` put `f x - wₙ ^ p` in the same ideal.
Thus `w ^ p - f x` lies in every `(s ^ (p * n))`, and hence every `(s ^ n)` since `p ≥ 2`.
The separatedness included in adic completeness makes this difference zero.
The DVR and completeness notions are `def-sc-discrete-valuation-ring` and
`def-weil-pbc-adically-complete-ring`. -/
theorem exists_frobenius_digits_or_root
    (R : Type u) (S : Type v) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [IsAdicComplete (IsLocalRing.maximalIdeal S) S]
    (p : ℕ) (hp : p.Prime) [CharP R p] [CharP S p]
    (f : R →+* S) (hf : Function.Injective f) [IsLocalHom f]
    (t : R) (s : S) (ht : Irreducible t) (hs : Irreducible s) (hst : s ^ p = f t)
    (x : R) :
    (∃ (m : ℕ) (c : Fin m → R) (b : R),
      x = (∑ i : Fin m, c i ^ p * t ^ (i : ℕ)) + b * t ^ m ∧
      ¬ ∃ z : R ⧸ Ideal.span ({t} : Set R),
        z ^ p = Ideal.Quotient.mk (Ideal.span ({t} : Set R)) b) ∨
    (∃ w : S, w ^ p = f x) := by
  sorry

end IsDiscreteValuationRing
