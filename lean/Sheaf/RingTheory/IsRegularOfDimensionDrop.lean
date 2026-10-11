/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Sheaf.RingTheory.Depth

/-!
# Dimension drop gives a regular sequence in a Cohen-Macaulay local ring

Source: Stacks Project, Algebra, Proposition 10.103.4 (Tag 00N6), first assertion for
`M = R`; Definition 10.103.1 (Tag 00N3)
(blueprint: lem-weil-pbc-cm-local-dimension-drop-regular-sequence).
-/

universe u

namespace RingTheory.Sequence

/-- In a finite-dimensional Cohen-Macaulay Noetherian local ring, a list in the maximal
ideal cutting the dimension by its length is regular. Source: Stacks, Tag 00N6, first
assertion for `M = R`; Tag 00N3
(blueprint: lem-weil-pbc-cm-local-dimension-drop-regular-sequence).

Proof plan:
1. Put `I_i = (gs.take i)` and `M_i = R/I_i`. These are finite nonzero modules, since
   `I_i` lies in the maximal ideal. Their annihilators are `I_i`, so their supports are
   `V(I_i)` by lem-weil-pbc-finite-module-support-annihilator. Prime-ideal correspondence
   identifies their support dimensions with the dimensions of the quotient rings.
2. The bound lem-weil-pbc-support-dimension-quotient-element-bound says each step decreases
   dimension by at most one. Summing the bounds before and after each index, and using
   the final dimension hypothesis, shows `dim Supp(M_i) = d - i` at every step.
3. By lem-weil-pbc-depth-le-support-dimension and the depth hypothesis, `M_0 = R` has
   depth equal to support dimension, hence is Cohen-Macaulay.
4. Inductively apply lem-weil-pbc-cm-module-good-element-nonzerodivisor to `M_i` and the
   next element: it is injective on `M_i`, and `M_{i+1}` is again Cohen-Macaulay.
5. These injectivity statements and the nonzero final quotient give `IsRegular R gs`.
   For the empty list, regularity follows from the nonzero ring.

The additive dimension equality encodes integer subtraction without truncating `d - c`.
-/
theorem isRegular_of_dimension_drop {R : Type u} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] (d : ℕ) (hd : ringKrullDim R = (d : WithBot ℕ∞))
    (hdepth : (d : ℕ∞) ≤ IsLocalRing.depth (R := R) R) (gs : List R)
    (hmem : ∀ g ∈ gs, g ∈ IsLocalRing.maximalIdeal R)
    (hdrop : ringKrullDim (R ⧸ Ideal.ofList gs) + (gs.length : WithBot ℕ∞) =
      (d : WithBot ℕ∞)) :
    IsRegular R gs := by
  sorry

end RingTheory.Sequence
