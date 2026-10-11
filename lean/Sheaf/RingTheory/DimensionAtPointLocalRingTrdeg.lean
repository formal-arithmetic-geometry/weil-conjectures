/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.RingTheory.KrullDimension.Basic
import WeilConjectures.Mathlib.Topology.KrullDimension

/-!
# Dimension at a point of a finite type algebra over a field

Source: Stacks Project, Algebra, Lemma 00P1
(`lemma-dimension-at-a-point-finite-type-field`)
(blueprint: lem-weil-pbc-dimension-at-point-local-ring-trdeg).
-/

universe u v

namespace AlgebraicGeometry

/-- Source: Stacks Project, Algebra, Lemma 00P1
(`lemma-dimension-at-a-point-finite-type-field`).
(blueprint: lem-weil-pbc-dimension-at-point-local-ring-trdeg).
The local topological dimension, local-ring dimension, and residue-field transcendence degree
are finite, and the first is the sum of the other two. Natural-number witnesses express
finiteness without losing the cardinal-valued meaning of `Algebra.trdeg`.

Proof:
1. Set r = trdeg_k κ(p). The spectrum of S/p is V(p), and its fraction field is κ(p).
   By `lem-weil-pbc-finite-type-domain-dimension-trdeg`, its dimension is r and is finite.
   By `lem-weil-pbc-finite-type-domain-dimension-local-ring`, a maximal chain above p
   has length r.
2. By `lem-weil-pbc-finite-type-algebra-noetherian` and
   `lem-weil-pbc-noetherian-finitely-many-minimal-primes`, S has finitely many minimal primes.
   Those q_j below p form a nonempty list by `lem-weil-pbc-prime-contains-minimal-prime`.
   By `lem-weil-pbc-localization-prime-residue-field-iso`, they correspond to the minimal
   primes of S_p.
3. Choose maximal chains from each q_j to p, of lengths s(j). By
   `lem-weil-pbc-localization-dimension-chains-below-prime` and the prime correspondence,
   dim S_p = max_j s(j), which is finite.
4. By `lem-weil-pbc-dimension-at-point-components`, dim_p Spec S = max_j dim(S/q_j).
   Concatenate each chain below p with the chain above p. By
   `lem-weil-pbc-finite-type-domain-dimension-local-ring`, dim(S/q_j) = s(j) + r.
   Taking maxima gives dim_p Spec S = dim S_p + r, also finite. -/
theorem topologicalKrullDimAt_eq_ringKrullDim_add_trdeg
    {k : Type u} [Field k] {S : Type v} [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (p : Ideal S) [p.IsPrime] :
    ∃ d r : ℕ,
      ringKrullDim (Localization.AtPrime p) = (d : WithBot ℕ∞) ∧
      Algebra.trdeg k p.ResidueField = (r : Cardinal.{v}) ∧
      topologicalKrullDimAt (⟨p, inferInstance⟩ : Spec (CommRingCat.of S)) =
        ((d + r : ℕ) : WithBot ℕ∞) := by
  sorry

end AlgebraicGeometry
