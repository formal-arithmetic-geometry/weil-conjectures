/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
import Mathlib.RingTheory.Support
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.GDelta.Basic

/-!
# Removing embedded associated primes

Source: Stacks Project, Tag 02M6, `algebra-lemma-remove-embedded-primes`
(blueprint: lem-sc-hilbert-embedded-points-affine-removal).
-/

universe u v

namespace Module

/-- A finite module over a Noetherian commutative ring has a maximal submodule with
nowhere dense support in its own support. The quotient has the same support and no
embedded associated primes, and the localized quotient map is an isomorphism away from
any element belonging to every embedded associated prime of the original module.
`IsNowhereDense` is evaluated in the subspace `Module.support R M`.
Under the Noetherian hypothesis, `isAssociatedPrime_iff` identifies Mathlib's associated
primes with the annihilators of elements, as required here.

Source: Stacks Project, Tag 02M6, `algebra-lemma-remove-embedded-primes`
(blueprint: lem-sc-hilbert-embedded-points-affine-removal).

Proof for stage 3, following the four steps of the DAG node:
1. By `lem-weil-pbc-noetherian-associated-primes-finite` and
`lem-weil-pbc-minimal-support-prime-associated`, partition the associated primes into
minimal support primes q_j and embedded primes p_i. An element with annihilator p
stays nonzero at p: otherwise an element outside p would annihilate it.
2. Take K to consist of elements whose cyclic module has support in the union of the
closed sets V(p_i). Support of a sum is contained in the union of the two cyclic supports,
so K is a submodule. By `lem-weil-pbc-noetherian-submodule-finite`, K is finite and its
support is closed. This support avoids every generic point q_j, hence is nowhere dense
in the support of M (Stacks Tag 0052).
3. A submodule L with nowhere dense support vanishes at every q_j. For each element of L,
any minimal prime of its cyclic support is associated to that cyclic module by
`lem-weil-pbc-minimal-support-prime-associated`, and to M by
`lem-weil-pbc-associated-prime-submodule`. It cannot be a q_j, so it is a p_i.
Thus its cyclic support lies in the union of V(p_i), giving L ≤ K and maximality.
4. Localization of K at each q_j vanishes, so the quotient has the same closed support
as M. If q annihilates a nonzero quotient element, a lift has cyclic support containing
some q_j, by the same two associated-prime lemmas. The quotient element remains nonzero
at q_j, forcing q ≤ q_j; minimality in the common support gives equality. Thus every
associated prime of the quotient is minimal. Finally f in every p_i has D(f) disjoint
from the support of K. Localization gives K_f = 0, so the localized quotient map is
bijective, using `def-weil-pbc-module-localization`. -/
theorem exists_maximal_nowhereDense_support_quotient
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ K : Submodule R M,
      Maximal (fun L : Submodule R M =>
        IsNowhereDense {p : Module.support R M | p.val ∈ Module.support R L}) K ∧
      Module.support R (M ⧸ K) = Module.support R M ∧
      (∀ p : Ideal R, p ∈ associatedPrimes R (M ⧸ K) →
        Minimal (fun q : Ideal R => q ∈ associatedPrimes R (M ⧸ K)) p) ∧
      (∀ f : R,
        (∀ p : Ideal R, p ∈ associatedPrimes R M →
          ¬ Minimal (fun q : Ideal R => q ∈ associatedPrimes R M) p → f ∈ p) →
        Function.Bijective
          (IsLocalizedModule.map (Submonoid.powers f)
            (LocalizedModule.mkLinearMap (Submonoid.powers f) M)
            (LocalizedModule.mkLinearMap (Submonoid.powers f) (M ⧸ K)) K.mkQ)) := by
  sorry

end Module
