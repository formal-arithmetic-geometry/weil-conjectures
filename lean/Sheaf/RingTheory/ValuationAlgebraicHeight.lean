/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q56
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Algebraic extensions preserve valuation height

Source: Temkin, Stable modification of relative curves, §2.1, p. 7; Stacks Project,
Algebra, Tags 052L and 090Q, and More on Algebra, Tag 0ASJ, first proof paragraph
(blueprint: lem-trf-valuation-algebraic-height).

Contraction identifies the ordered prime spectra of a valuation subring and its
restriction to an algebraic subfield, and hence their Krull dimensions, with infinite
height allowed. The restricted valuation subring is Mathlib's `ValuationSubring.comap`.
-/

@[expose] public section

universe u v

namespace ValuationSubring

/-- Algebraic extension preserves the prime-ideal order and valuation height.
Source: Temkin, Stable modification of relative curves, §2.1, p. 7; Stacks Project,
Tags 052L and 090Q, and Tag 0ASJ, first proof paragraph
(blueprint: lem-trf-valuation-algebraic-height).

Here `V.comap (algebraMap K E)` is `A = V ∩ K`, already bundled as a valuation subring.
The equality specifying `e` identifies its forward map with contraction along the
restriction of the given field embedding. Krull dimension is the supremum of lengths
of finite strict prime-ideal chains; its value may be infinite.

Proof plan:
1. Restrict the valuation alternative to `K`, obtaining the valuation subring `A`.
   In either valuation ring, divisibility of nonzero elements is total, so every finite
   nonempty list of nonzero elements has one dividing all the others (Tags 052L, 090Q).
2. For an ideal `I` of `A`, its extension `IV` contracts to `I`: in a nonzero finite
   sum `b = ∑ aᵢvᵢ` belonging to `A`, choose a nonzero coefficient `aⱼ` dividing all
   coefficients. Then `b/aⱼ ∈ V ∩ K = A`, so `b ∈ I`. Zero and the reverse inclusion
   are immediate.
3. For a prime `q` of `A`, put `P(q) = radical(qV)`. The radical is an ideal:
   if `xⁿ, yᵐ ∈ qV`, the binomial expansion gives `(x+y)^(n+m) ∈ qV`;
   scalar multiplication and negation preserve power membership. Step 2 and primeness
   of `q` give `P(q) ∩ A = q`, hence `P(q)` is proper.
4. It is prime: if `(xy)ⁿ ∈ qV`, total divisibility gives `y = xc` or `x = yc`
   for `c ∈ V`. Respectively `y^(2*n) = (xy)ⁿcⁿ` or `x^(2*n) = (xy)ⁿcⁿ`
   belongs to `qV`. A zero factor is already in the radical.
5. Use `lem-trf-valuation-value-group-torsion`: every nonzero `x ∈ V` has
   `xⁿ = au`, with `n ≥ 1`, `a ∈ K` nonzero and `u` a unit in `V`.
   Then `a = xⁿu⁻¹ ∈ A`. For a prime `p` of `V`, writing `q = p ∩ A`,
   primeness and invertibility of `u` imply `x ∈ p` iff `a ∈ q`.
   Thus `p ⊆ P(q)`; the converse follows from `qV ⊆ p` and primeness of `p`.
   Zero is in both ideals. Hence `P(p ∩ A) = p`.
6. Steps 3 and 5 give inverse bijections. Contraction preserves inclusion, as does
   `q ↦ radical(qV)`, so the specified contraction is an order isomorphism.
   Applying it and its inverse to finite strict chains preserves length; the suprema
   are equal, including when these lengths are unbounded. -/
theorem primeSpectrum_comap_orderIso_of_isAlgebraic
    (K : Type u) (E : Type v) [Field K] [Field E] [Algebra K E]
    [Algebra.IsAlgebraic K E] (V : ValuationSubring E) :
    (∃ e : PrimeSpectrum V ≃o PrimeSpectrum (V.comap (algebraMap K E)),
      ∀ p : PrimeSpectrum V,
        e p = PrimeSpectrum.comap
          ((algebraMap K E).restrict (V.comap (algebraMap K E)) V (fun _ hx ↦ hx)) p) ∧
    ringKrullDim V = ringKrullDim (V.comap (algebraMap K E)) := by
  sorry

end ValuationSubring
