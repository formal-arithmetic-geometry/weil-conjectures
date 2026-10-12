/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import Sheaf.RingTheory.NagataRing
public import Mathlib.RingTheory.Algebraic.Defs

/-!
# Algebraic monogenic extensions of Nagata domains are Japanese

Source: Stacks Project, Algebra, Proposition Tag 0334, claim (**) and Step 4
(blueprint: lem-weil-pbc-algebraic-monogenic-nagata-domain-n2).
-/

@[expose] public section

universe u

/-- An algebraic injective monogenic extension of Nagata domains is N-2.

Source: Stacks Project, Algebra, Proposition Tag 0334, claim (**) and Step 4
(blueprint: lem-weil-pbc-algebraic-monogenic-nagata-domain-n2).

Proof: Write `K = Frac(A)` and `L = Frac(B)`; injectivity embeds `K` in `L`.
Clearing denominators identifies algebraicity over `A` with algebraicity over `K`.
Since `x` generates `B`, it generates `L` as a field over `K`, so `L/K` is finite.
For any finite extension `M/L`, the tower law makes `M/K` finite. The integral
closure `A'` of `A` in `M` is finite over `A` by N-2 (the zero prime of the Nagata
hypothesis), normal with fraction field `M`, and Nagata by Tag 032T. Inside `M`,
put `T = A'[x]`. The finite module generators of `A'` over `A` generate `T` over
`B`: expand coefficients of each polynomial in `x` in those generators. Thus
`T/B` is finite, hence integral, and `Frac(T) = M` since `A'` is contained in `T`.
The integral closures of `B` and `T` in `M` agree: integrality over `B` implies
integrality over `T` by the same equation; conversely use transitivity through
`T/B`. Claim (***) of Tag 0334 makes `T` N-1, so this closure is finite over `T`.
Finiteness transitivity makes it finite over `B`. Varying `M/L` proves N-2.

No normality of `A` is needed: only `A'` must be normal. If `x = 0` or is in the
image of `A`, `L = K` and the same argument applies. -/
theorem isN2_of_algebraic_monogenic_nagata_domain (A B : Type u) [CommRing A] [IsDomain A]
    [CommRing B] [IsDomain B] [Algebra A B] (hA : IsNagataRing A)
    (hinj : Function.Injective (algebraMap A B)) (x : B)
    (hgen : Algebra.adjoin A ({x} : Set B) = ⊤) (hx : IsAlgebraic A x) :
    IsN2 B (FractionRing B) := by sorry
