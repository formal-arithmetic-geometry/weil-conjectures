/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.RingTheory.Depth
public import Mathlib.RingTheory.KrullDimension.Regular
import Sheaf.RingTheory.CmModuleGoodElementNonzerodivisor
import Sheaf.RingTheory.DepthLeSupportDimension

/-!
# Cohen–Macaulay quotients by a nonzerodivisor

Source: Stacks Project, Algebra, Lemma 10.104.2 (Tag 02JN), last assertion for one
regular element (blueprint: lem-weil-pbc-cm-local-quotient-nonzerodivisor-cm).
-/

@[expose] public section

universe u

namespace IsLocalRing

/-- A quotient of a Noetherian local Cohen–Macaulay ring by a nonzerodivisor in its
maximal ideal is again Cohen–Macaulay, of dimension one less (Stacks, Tag 02JN)
(blueprint: lem-weil-pbc-cm-local-quotient-nonzerodivisor-cm).

Proof, following the DAG's five steps:
1. Since `x` lies in the maximal ideal, its principal ideal is proper. The quotient is
nonzero, Noetherian and local, with maximal ideal the image of the original maximal ideal.
The dimension-quotient-nonzerodivisor lemma gives dimension plus one equal to `d`, hence
`d ≥ 1` and quotient dimension `d - 1`.
2. The support-annihilator lemma identifies the supports of `S` and `S/xS` with `Spec S`
and `V(x)`. Prime correspondence identifies the dimension of `V(x)` with that of the
quotient, so intersecting the support with `V(x)` decreases dimension by one.
3. The depth-le-support-dimension lemma and the assumed depth bound show that `S` is a
Cohen–Macaulay module over itself, of depth `d`.
4. The cm-module-good-element-nonzerodivisor lemma (Stacks, Tag 00N5, clause (b)) gives
`S/xS` depth `d - 1` as an `S`-module and makes it Cohen–Macaulay over `S`.
5. Choose a regular sequence of this length in the maximal ideal using the definition
of depth. Its images in the quotient maximal ideal act by the same maps on every
successive module quotient. They therefore form a regular sequence over `S/xS` itself,
which gives the asserted quotient-ring depth bound (change of rings, Tag 0AAD).
-/
theorem depth_quotient_nonzerodivisor
    (S : Type u) [CommRing S] [IsNoetherianRing S] [IsLocalRing S]
    (d : ℕ) (hd : ringKrullDim S = (d : WithBot ℕ∞))
    (hdepth : (d : ℕ∞) ≤ depth (R := S) S) (x : S)
    (hx : x ∈ maximalIdeal S) (hregular : x ∈ nonZeroDivisors S) :
    ∃ hQ : IsLocalRing (S ⧸ Ideal.span {x}),
      letI := hQ
      IsNoetherianRing (S ⧸ Ideal.span {x}) ∧
      ringKrullDim (S ⧸ Ideal.span {x}) = ((d - 1 : ℕ) : WithBot ℕ∞) ∧
      maximalIdeal (S ⧸ Ideal.span {x}) =
        (maximalIdeal S).map (Ideal.Quotient.mk (Ideal.span {x})) ∧
      ((d - 1 : ℕ) : ℕ∞) ≤ depth (R := S ⧸ Ideal.span {x}) (S ⧸ Ideal.span {x}) ∧
      ∃ rs : List (S ⧸ Ideal.span {x}),
        RingTheory.Sequence.IsRegular (S ⧸ Ideal.span {x}) rs ∧
        (∀ y ∈ rs, y ∈ maximalIdeal (S ⧸ Ideal.span {x})) ∧ rs.length = d - 1 := by
  sorry

end IsLocalRing
