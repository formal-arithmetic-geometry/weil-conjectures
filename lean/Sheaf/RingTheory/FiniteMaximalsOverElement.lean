/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.KrullDimension.Basic

/-!
# Finitely many maximal ideals over a nonzero element

Source: Stacks Project, Algebra, Lemma Tag 00PF (blueprint:
lem-sc-finite-maximals-over-element).
-/

universe u

namespace Ring

/-- For a one-dimensional Noetherian domain, only finitely many maximal ideals contain
any fixed nonzero element (Stacks, Tag 00PF).
(blueprint: lem-sc-finite-maximals-over-element)

Proof: For `I = xR`, the minimal primes over `I` form a finite set by
`lem-sc-finite-minimal-primes-over-ideal`. Any maximal ideal containing `x` contains one
of these minimal primes by `lem-weil-pbc-prime-contains-minimal-prime`. Since `R` is a domain,
that prime is nonzero; the dimension-one hypothesis forces it to equal the maximal ideal.
Thus the maximal ideals in question form a subset of a finite set. -/
theorem finite_maximalIdeals_containing_nonzero
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (h_dim : ringKrullDim R = 1) (x : R) (hx : x ≠ 0) :
    Set.Finite {m : Ideal R | m.IsMaximal ∧ x ∈ m} := by
  sorry

end Ring
