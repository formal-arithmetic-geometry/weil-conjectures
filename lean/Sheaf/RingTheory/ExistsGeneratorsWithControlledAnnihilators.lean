/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: E1
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Sheaf.AlgebraicGeometry.Ogoma
import Sheaf.RingTheory.RegularLocalGeneratorsRegularSequence
import Sheaf.RingTheory.RegularSequencePowers

/-!
# Generators of a regular prime with controlled annihilators

Source: Stacks Project, Smoothing Ring Maps, Lemma 07FD
(blueprint: lem-weil-pbc-popescu-find-sequence).
-/

@[expose] public section

universe u

namespace Ideal

/-- Source: Stacks Project, Lemma 07FD
(blueprint: lem-weil-pbc-popescu-find-sequence).
The exponent `n` is the given exponent, as obtained by the source's proof.

Proof: Set S = R \ q. Lift d generators of the maximal ideal of the regular local ring
R_q to numerators in R. Their n-th powers belong to I after localization; clearing
denominators and multiplying each generator by an element of S puts these powers in I.
Both generation after localization and membership of the n-th powers in I persist under
further multiplication by elements of S. Induct on the length of the initial segment for
which the annihilator equality holds. The localized generators form a regular sequence
by 00NQ (lem-weil-pbc-regular-local-generators-regular-sequence), and their positive powers
are regular by 07DV (lem-weil-pbc-regular-sequence-powers). Thus the next generator and
its square both act injectively on the localized quotient by previous e-th powers.
Localization is exact (lem-weil-pbc-localization-module-exact), identifying this quotient
with the localization of the finitely generated module R modulo the previous powers.
Ogoma's lemma 07FC (lem-weil-pbc-ogoma) then supplies an element of S whose product with
the next generator has equal annihilators for its first and second powers on that module.
This preserves all preceding conditions, completing the induction. -/
theorem exists_generators_with_controlled_annihilators
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I q : Ideal R) [q.IsPrime] (hIq : I ≤ q)
    (n e d : ℕ) (hn : 0 < n) (he : 0 < e)
    (hpow : (q ^ n).map (algebraMap R (Localization.AtPrime q)) ≤
      I.map (algebraMap R (Localization.AtPrime q)))
    [IsRegularLocalRing (Localization.AtPrime q)]
    (hdim : ringKrullDim (Localization.AtPrime q) = (d : WithBot ℕ∞)) :
    ∃ π : Fin d → R,
      Ideal.span (Set.range (fun i ↦ algebraMap R (Localization.AtPrime q) (π i))) =
        q.map (algebraMap R (Localization.AtPrime q)) ∧
      (∀ i : Fin d, π i ^ n ∈ I) ∧
      (∀ i : Fin d,
        {m : R ⧸ Ideal.span {x : R | ∃ j : Fin d, j < i ∧ x = π j ^ e} | π i • m = 0} =
          {m : R ⧸ Ideal.span {x : R | ∃ j : Fin d, j < i ∧ x = π j ^ e} |
            π i ^ 2 • m = 0}) := by
  sorry

end Ideal
