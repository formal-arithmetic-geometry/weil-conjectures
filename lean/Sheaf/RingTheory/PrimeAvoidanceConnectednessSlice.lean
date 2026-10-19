/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q18
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Topology.KrullDimension
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Topology.NoetherianSpace
import Sheaf.RingTheory.PuncturedLocalClosedPoints

/-!
# Cutting a closed subset while meeting locally closed pieces

Source: Stacks Project, Tag 0ECR, second half of the proof of
`lemma-punctured-still-connected`, and Tag 02J6(4)
(blueprint: lem-per-prime-avoidance-connectedness-slice).
-/

@[expose] public section

universe u

namespace PrimeSpectrum

/-- A closed subset of dimension `e` in a finite-dimensional Noetherian local spectrum
can be cut down to its closed point by `e` equations, while their common zero locus
meets every member of a finite family of nonempty locally closed subsets of the
punctured complement. The family may be empty. Locally closedness is expressed in
the ambient spectrum: the punctured complement of `T` is open, so this is equivalent
to locally closedness in that complement.

Source: Stacks Project, Tag 0ECR, second half of the proof of
`lemma-punctured-still-connected`; Tag 02J6(4) supplies closed points of the puncture
(blueprint: lem-per-prime-avoidance-connectedness-slice).

Proof: (1) The ideal description of closed subsets and the radical formula, using
`lem-weil-pbc-spec-irreducible-closed-subsets-primes` and
`lem-weil-pbc-zero-locus-eq-iff-radical-eq`, show that the ascending chain condition
on ideals makes the spectrum and its closed subspaces Noetherian.
(2) Each prescribed locally closed set is locally closed in the puncture. By
`lem-per-punctured-local-closed-points`, choose a point `w_j` in it closed in the
puncture. Its prime `p_j` has zero locus exactly `{w_j, m}`. No choices are needed
for an empty family.
(3) Inductively construct `n` equations in `m` and all the `p_j`, with the cut of
`T` having dimension at most `e - n`. Every nonempty closed subset of a local
spectrum contains its closed point, so all cuts remain nonempty.
(4) By `lem-sc-noetherian-finite-irreducible-components`, each cut has finitely many
irreducible components. They cover it: a strict enlargement of an irreducible closed
subset extends a chain, so the finite dimension bound prevents indefinite enlargement.
Each component is `V(q)` for a prime `q`. For a positive-dimensional component,
`q` differs from `m` and contains none of the `p_j`, since `V(p_j) = {w_j, m}`
and `w_j` lies outside `T`.
(5) The ideal `J = m ∩ ⋂ j, p_j` lies in none of these component primes: multiply
an element of `m` outside `q` by one element of each `p_j` outside `q`.
(6) Apply `lem-weil-pbc-prime-avoidance` to obtain the next equation in `J` avoiding
all positive-dimensional component primes. If there are none, take zero instead.
(7) Any chain of irreducible closed subsets of the next cut lies in one component
of the preceding cut. If that component has positive dimension, append it strictly
to the chain; otherwise the chain has length zero. This reduces the dimension upper
bound by one, without catenarity or purity assumptions.
(8) After `e` steps the cut contains `m` and has dimension at most zero. Any other
prime would give a length-one chain from `{m}` to its closure, a contradiction.
Each equation belongs to every `p_j`, so every `w_j` survives. For `e = 0`, `T`
is already `{m}` and the empty list has the entire spectrum as its zero locus. -/
theorem exists_zeroLocus_inter_eq_closedPoint_meeting
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hfinite : topologicalKrullDim (AlgebraicGeometry.Spec (.of A)) < ⊤)
    (T : Set (AlgebraicGeometry.Spec (.of A))) (hTclosed : IsClosed T)
    (hTnonempty : T.Nonempty) (e : ℕ) (hTdim : topologicalKrullDim T = e)
    (s : ℕ) (W : Fin s → Set (AlgebraicGeometry.Spec (.of A)))
    (hWnonempty : ∀ j : Fin s, (W j).Nonempty)
    (hWlocallyClosed : ∀ j : Fin s, IsLocallyClosed (W j))
    (hWsubset : ∀ j : Fin s, W j ⊆ {IsLocalRing.closedPoint A}ᶜ \ T) :
    ∃ f : Fin e → A, (∀ i : Fin e, f i ∈ IsLocalRing.maximalIdeal A) ∧
      T ∩ zeroLocus (Set.range f) = {IsLocalRing.closedPoint A} ∧
      ∀ j : Fin s, (W j ∩ zeroLocus (Set.range f)).Nonempty := by
  sorry

end PrimeSpectrum
