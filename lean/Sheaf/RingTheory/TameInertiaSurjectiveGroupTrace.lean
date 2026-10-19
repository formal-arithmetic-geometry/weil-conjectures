/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Operations
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# Surjectivity of the group trace under tame inertia

Source: Stacks Project, `more-algebra.tex`, Tags 0BRH, 0BRI and 0BRJ, and the
agent-supplied semilocal trace argument in the stage-1 report for
`lem-per-tame-admissible-scheme-quotient`
(blueprint: lem-per-tame-inertia-surjective-group-trace).
-/

@[expose] public section

universe u v

namespace MulSemiringAction

/-- Tame residue inertia makes the group trace onto the fixed subring surjective,
expressed by a preimage for every invariant element, and gives a trace-one element.

Here `p.inertia G` is Mathlib's subgroup of elements acting trivially modulo `p`.
It stabilizes `p`, and acting trivially on `R / p` is equivalent to acting trivially
on its fraction field `p.ResidueField`; hence this is exactly residue inertia.
The sum is the usual group trace. Its invariance follows by reindexing the sum,
and it is linear over `FixedPoints.subring R G` since its scalars are fixed.

Source: Stacks Project, `more-algebra.tex`, Tags 0BRH, 0BRI and 0BRJ, with the
agent-supplied argument in the stage-1 report for `lem-per-tame-admissible-scheme-quotient`.
(blueprint: lem-per-tame-inertia-surjective-group-trace)

Proof (the node's seven steps):
1. For `h : G`, left multiplication permutes `G`, so `h (T r) = T r`; thus `T` takes
   values in `A = R^G`, is additive and satisfies `T (a r) = a T r` for `a : A`.
   Hence `J = T(R)` is an ideal of `A`; it suffices that no maximal ideal contains it.
2. For `r : R` the monic orbit polynomial `∏ g, (X - g r)` has coefficients in `A`
   (each `h` permutes its factors) and vanishes at `r`, so `A → R` is integral
   (Stacks 0BRI). No finite-generation assumption is used.
3. Fix a maximal ideal `m` of `A`. Lying over for the injective integral map
   (Stacks 00GQ) gives a prime `p` of `R` over `m`, maximal by the prime-over-maximal
   lemma (Stacks 00GS (3)). The orbit `O = {g p}` is a finite set of maximal ideals.
4. `k = R / p` is a field, canonically `κ(p)` (via `r / s ↦ r̄ s̄⁻¹`). Let `D` be the
   stabilizer of `p` and `H` its image in `Aut k`. The kernel of `D → H` is `I_p`, so
   each fibre is a coset `d I_p` with `|I_p|` elements.
5. By independence of characters (Stacks 0CKL) applied to the distinct maps in `H`
   with all coefficients `1`, `∑ σ ∈ H, σ` is not zero; choose `b : k` with
   `u = ∑ σ ∈ H, σ b ≠ 0`.
6. Distinct ideals of `O` are comaximal; the Chinese remainder theorem (Stacks 00DT)
   gives `r : R` with residue `b` at `p` and `0` at the other ideals of `O`. If
   `g ∉ D` then `g r ∈ p`; if `g ∈ D` the residue of `g r` is `ḡ b`. Counting fibres,
   `T r ≡ |I_p| u ≠ 0 (mod p)` by tameness, so `T r ∉ p ∩ A = m`.
7. Hence no maximal ideal of `A` contains `J`; by the maximal-ideal lemma
   (Stacks 00E0) `J = A`. So `T a = 1` for some `a`, and `c = T (c a)` for every
   `c : A`; conversely surjectivity gives a preimage of `1`. In the zero ring
   `T 0 = 0 = 1` and there are no maximal ideals.
No Noetherianity, finite type, faithfulness or invertibility of `|G|` is used. -/
theorem groupTrace_surjective_of_isUnit_inertia
    (R : Type u) [CommRing R] (G : Type v) [Group G] [Fintype G]
    [MulSemiringAction G R]
    (htame : ∀ (p : Ideal R) [p.IsPrime],
      IsUnit (Nat.card (p.inertia G) : p.ResidueField)) :
    (∀ b : FixedPoints.subring R G, ∃ a : R, ∑ g : G, g • a = (b : R)) ∧
      (∃ a : R, ∑ g : G, g • a = 1) := by
  sorry

end MulSemiringAction
