/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Regular.RegularSequence
public import Sheaf.RingTheory.IsRegularSystemOfParameters

/-!
# Regular systems of parameters and regular sequences

Source: Stacks Project, Algebra, Lemma 00NQ and Definition 00KU
(blueprint: lem-weil-pbc-regular-local-generators-regular-sequence).

## Main statements

* `IsRegularLocalRing.isRegular_and_quotients_of_generators`: regularity of a system of
  parameters, its initial quotients, and all its permutations.
* `IsRegularLocalRing.minimal_generators_iff_card_eq_dimension`: the parenthetical
  characterization of minimal generating sets in the node.
-/

@[expose] public section

universe u

namespace IsRegularLocalRing

/-- Stacks Project, Algebra, Lemma 00NQ and Definition 00KU
(blueprint: lem-weil-pbc-regular-local-generators-regular-sequence).
A regular system of parameters (`def-weil-pbc-regular-system-of-parameters`: `d` elements
generating the maximal ideal) is a regular sequence; its first `c` elements cut out a regular
local quotient of dimension `d - c`. Every permutation is again a regular system of parameters
and is regular.

Proof (steps 2--6 of the node): induct on `d`, simultaneously for all regular local rings.
For `d = 0`, the maximal ideal is zero and the empty sequence is regular since a local ring
is nonzero (`def-weil-pbc-regular-sequence`); the only quotient is the ring itself.
For `d > 0`, the first generator is nonzero by the bound on dimension in terms of the number
of generators (`lem-weil-pbc-noetherian-local-dimension-le-generators`). The ring is a domain
(`lem-sc-regular-local-domain`), so this generator is a nonzerodivisor. Its quotient is local
(`lem-weil-pbc-quotient-local-structure`) and Noetherian
(`lem-weil-pbc-surjective-image-noetherian`); its dimension is `d - 1`
(`lem-weil-pbc-dimension-quotient-nonzerodivisor`). The remaining `d - 1` generators span its
maximal ideal, so the quotient is regular local (`def-weil-regular-scheme`). Apply induction
there. The third isomorphism theorem identifies its successive quotients with the original
initial quotients and intertwines multiplication by the remaining generators, proving both
regularity and the quotient assertions. Finally apply the same result to any permutation,
which has the same length and generates the same ideal. -/
theorem isRegular_and_quotients_of_generators
    (R : Type u) [CommRing R] [IsRegularLocalRing R] (d : ℕ)
    (hd : ringKrullDim R = (d : WithBot ℕ∞)) (rs : List R)
    (hrs : IsLocalRing.IsRegularSystemOfParameters rs) :
    RingTheory.Sequence.IsRegular R rs ∧
      (∀ c : ℕ, c ≤ d →
        IsRegularLocalRing (R ⧸ Ideal.ofList (rs.take c)) ∧
          ringKrullDim (R ⧸ Ideal.ofList (rs.take c)) = ((d - c : ℕ) : WithBot ℕ∞)) ∧
      (∀ ys : List R, rs.Perm ys →
        IsLocalRing.IsRegularSystemOfParameters ys ∧ RingTheory.Sequence.IsRegular R ys) := by
  sorry

/-- Stacks Project, Algebra, Definition 00KU and Lemma 00NQ
(blueprint: lem-weil-pbc-regular-local-generators-regular-sequence).
Among finite sets generating the maximal ideal of a regular local ring of dimension `d`,
the minimal ones are exactly those of cardinality `d`.

Proof (step 1 of the node): a proper subset of a set of `d` generators has fewer than `d`
elements, so cannot generate the maximal ideal by the dimension bound
(`lem-weil-pbc-noetherian-local-dimension-le-generators`). Conversely, images of a minimal
set of generators form a basis of the cotangent space: they span, and a linear dependence
would allow deletion of a generator by Nakayama (`lem-weil-pbc-nakayama-local-generators`).
The cotangent space is spanned by some `d` generators by regularity
(`def-weil-regular-scheme`), so that basis has at most `d` members. The dimension bound gives
at least `d` members, hence exactly `d`. -/
theorem minimal_generators_iff_card_eq_dimension
    (R : Type u) [CommRing R] [IsRegularLocalRing R] (d : ℕ)
    (hd : ringKrullDim R = (d : WithBot ℕ∞)) (s : Finset R)
    (hspan : Ideal.span (s : Set R) = IsLocalRing.maximalIdeal R) :
    (∀ t : Finset R, t ⊂ s → Ideal.span (t : Set R) ≠ IsLocalRing.maximalIdeal R) ↔
      s.card = d := by
  sorry

end IsRegularLocalRing
