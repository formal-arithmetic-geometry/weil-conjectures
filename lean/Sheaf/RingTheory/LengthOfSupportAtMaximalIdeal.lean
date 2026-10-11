/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
import Mathlib.RingTheory.Support
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Positive finite length for a module supported at the maximal ideal

Source: Stacks Project, Algebra, Lemma 10.62.3 (Tag 00L5)
(blueprint: lem-sc-generic-stalk-finite-length).
-/

universe u v

namespace Module

/-- A nonzero finite module over a Noetherian local ring whose support is contained in
its maximal ideal has positive finite length. Source: Stacks Project, Algebra, Tag 00L5
(blueprint: lem-sc-generic-stalk-finite-length).

Proof: Let `J` be the annihilator of `M`. By
`lem-weil-pbc-finite-module-support-annihilator`, every prime containing `J` is the
maximal ideal. By `lem-weil-pbc-zero-locus-eq-iff-radical-eq`, the radical of `J`
contains the maximal ideal. Since that ideal is finitely generated, the radical-power
lemma `lem-weil-pbc-fg-ideal-radical-power` gives a positive power contained in `J`.
Thus some power of the maximal ideal annihilates `M`.

Filter `M` by the powers of the maximal ideal down to zero. Each successive quotient
is a finite-dimensional vector space over the residue field: finiteness follows from
`lem-weil-pbc-noetherian-submodule-finite`, and the maximal ideal acts by zero.
A finite flag of vector subspaces gives finite length for each quotient. Successive
applications of `lem-weil-pbc-length-additive-short-exact` give finite length for `M`.
Finally, since `M` is nonzero, the strict chain from zero to `M` has length one, so the
finite length is positive. -/
theorem length_eq_nat_of_support_subset_maximalIdeal
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (h_support : ∀ p ∈ Module.support R M, p.asIdeal = IsLocalRing.maximalIdeal R) :
    ∃ n : ℕ, 0 < n ∧ Module.length R M = (n : ℕ∞) := by
  sorry

end Module
