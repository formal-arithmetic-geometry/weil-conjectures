/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# A cyclic presentation of an ideal-power torsion module

Source: Stacks Project, More on Algebra, Tag 05E8, proof, first two sentences
(blueprint: lem-weil-pbc-torsion-cyclic-presentation).
-/

@[expose] public section

universe u v

open DirectSum

namespace Ideal

/-- An ideal-power torsion module has a surjection from a direct sum of positive-power
ideal quotients, with ideal-power torsion kernel and the resulting short exact sequence.
Source: Stacks Project, Tag 05E8, proof, first two sentences
(blueprint: lem-weil-pbc-torsion-cyclic-presentation).

Proof: Index the summands by the elements `q` of `Q`. Choose the least positive `n_q`
annihilating `q`. The map `R / I ^ n_q → Q` taking the class of `r` to `r • q` is well
defined and linear, since every element of `I ^ n_q` kills `q`
[def-weil-pbc-quotient-module]. Combine these maps by the direct sum universal property
[def-weil-pbc-direct-sum-modules]; the image of `1` in the `q`-summand is `q`, so the
resulting map is surjective. Every element of the direct sum has finite support. The
maximum of `1` and the exponents of its nonzero components annihilates it: the corresponding
ideal power is contained in each component's annihilating ideal power. Thus the direct
sum and its kernel are ideal-power torsion. Finally the kernel inclusion is injective,
its image is precisely the kernel, and the presentation map is surjective. This gives
short exactness [def-weil-pbc-exact-sequence], in the abelian category of modules
[lem-weil-pbc-ring-modules-grothendieck-abelian]. -/
theorem exists_torsion_cyclic_presentation {R : Type u} [CommRing R] (I : Ideal R)
    (Q : Type (max u v)) [AddCommGroup Q] [Module R Q]
    (hQ : ∀ q : Q, ∃ n : ℕ, 0 < n ∧ ∀ a ∈ I ^ n, a • q = 0) :
    ∃ (J : Type (max u v)) (n : J → ℕ), (∀ j : J, 0 < n j) ∧
      ∃ p : (⨁ j : J, R ⧸ I ^ n j) →ₗ[R] Q,
        Function.Surjective p ∧
        (∀ k : LinearMap.ker p, ∃ m : ℕ, 0 < m ∧ ∀ a ∈ I ^ m, a • k = 0) ∧
        p.shortComplexKer.ShortExact := by
  sorry

end Ideal
