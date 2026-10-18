/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q113
-/
module

public import Sheaf.GroupTheory.RationalRank
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Zero rational rank implies torsion

Source: Temkin, *Stable modification of relative curves*, §2.1, notation before
Lemma 2.1.2, and Proposition 4.3.1, proof, printed p. 28
(blueprint: lem-trf-rational-rank-zero-torsion).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AddCommGroup

/-- An abelian group of rational rank zero is elementwise torsion.

Source: Temkin, §2.1, notation before Lemma 2.1.2, and Proposition 4.3.1, proof,
printed p. 28 (blueprint: lem-trf-rational-rank-zero-torsion).

Proof plan:
1. By `def-trf-rational-rank`, the rationalization has cardinal dimension zero.
   A nonzero vector would give a linearly independent singleton, forcing dimension
   at least one. Thus the rationalization is zero, with no finiteness assumption.
2. Set `S` to the nonzero integers and use `def-weil-pbc-module-localization`.
   The fraction map identifies the localization of the integers with the rationals:
   equality of fractions reduces to cross multiplication, since the integers form
   a domain, and the fraction ring operations agree.
3. Apply `lem-weil-pbc-localization-tensor-over-base` with base and algebra the
   integers, first module the integers, and second module `G`. The tensor unit and
   symmetry maps from `def-weil-pbc-module-tensor-product` identify this with an
   additive isomorphism from the localization of `G` to its rationalization,
   sending `g / 1` to the pure tensor of `g` and `1`. Hence the localization is zero.
   The dependency definition orders the tensor factors as rationals then `G`,
   using the same canonical symmetry isomorphism.
4. The kernel criterion of `def-weil-pbc-module-localization` gives a nonzero
   integer `s` annihilating each `g`. Its absolute value, viewed as an integer,
   is at least one and also annihilates `g`, by changing the sign when necessary.
   This integer may depend on `g`.
-/
theorem exists_pos_zsmul_eq_zero_of_rationalRank_eq_zero
    (G : Type u) [AddCommGroup G] (h : rationalRank G = 0) :
    ∀ g : G, ∃ n : ℤ, 1 ≤ n ∧ n • g = 0 := by
  sorry

end AddCommGroup
