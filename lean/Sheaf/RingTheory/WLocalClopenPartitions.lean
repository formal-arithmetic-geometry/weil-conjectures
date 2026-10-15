/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import WeilConjectures.RingTheory.ProEtale.WLocal
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.Topology.Spectral.ConstructibleTopologyHausdorff

/-!
# Clopen partitions of a w-local affine spectrum

Source: blueprint, sec-proper-base-change/sk-thm-properbasechange,
node lem-weil-pbc-w-local-partition, order 1221
(blueprint: lem-weil-pbc-w-local-partition).
-/

@[expose] public section

universe u w

namespace PrimeSpectrum

/-- Patch compactness and the closed-point description of clopen partitions of a w-local
spectrum. Source: blueprint, sec-proper-base-change/sk-thm-properbasechange,
node lem-weil-pbc-w-local-partition, order 1221
(blueprint: lem-weil-pbc-w-local-partition).

Proof plan:
1. Affine schemes are quasi-compact and quasi-separated
   (`lem-weil-pbc-affine-scheme-qcqs`), hence spectral
   (`lem-weil-pbc-qcqs-scheme-spectral`). Basic opens form a basis and are affine localization
   spectra (`lem-weil-pbc-spec-localization-away-basic-open`), so quasi-compact opens are finite
   unions of basic opens. Thus their constructible topology is the patch topology. Apply
   `lem-weil-pbc-spectral-constructible-topology-quasi-compact` and
   `lem-weil-pbc-spectral-constructible-topology-hausdorff`.
2. Every prime lies in a maximal ideal (`lem-weil-pbc-proper-ideal-contained-in-maximal`).
   In the Zariski topology (`def-weil-affine-spectrum`), this is a closed specialization in
   the same component. By `def-weil-pbc-w-local` it is the unique closed point of that
   component; every point of the component specializes to it.
3. The closed point set is closed by w-locality, hence is the spectrum of a quotient
   (`lem-weil-pbc-spec-quotient-homeomorphism-zero-locus`). All primes of the quotient are
   maximal, so `lem-weil-pbc-zero-dimensional-spectrum-profinite` gives profiniteness.
4. Spectral components are intersections of clopen neighbourhoods
   (`def-weil-spectral-space`, `lem-weil-pbc-quasicompact-components-clopen-intersection`).
   Distinct closed points are therefore separated by clopens of the spectrum.
5. For a clopen part E of the closed point set, separate each c in E from each d outside E
   by such clopens. Compactness of the complement gives a finite intersection around c;
   compactness of E then gives a finite union extending E. Use the empty set or the whole
   space when either part is empty.
6. Every nonempty clopen contains the closed specialization of any of its points. Thus
   restriction is injective. A clopen partition of the compact closed point set has only
   finitely many nonempty parts; their unique lifts form a partition, since any nonempty
   overlap or uncovered complement would contain a closed point. Empty parts lift to empty
   parts. Restricting a partition preserves clopenness, disjointness, and the cover.
7. An open containing a closed point contains every point specializing to it. By step 2,
   it contains the entire component; apply this to every closed point of the given part. -/
theorem wLocal_clopen_partition_properties (A : Type u) [CommRing A] :
    (CompactSpace (WithConstructibleTopology (PrimeSpectrum A)) ∧
      T2Space (WithConstructibleTopology (PrimeSpectrum A))) ∧
    (IsWLocalRing A →
      (CompactSpace (closedPoints (PrimeSpectrum A)) ∧
        T2Space (closedPoints (PrimeSpectrum A)) ∧
        TotallyDisconnectedSpace (closedPoints (PrimeSpectrum A))) ∧
      (∀ (I : Type w) (P : I → Set (closedPoints (PrimeSpectrum A))),
        ((∀ i : I, IsClopen (P i)) ∧
          Pairwise (fun i j : I ↦ Disjoint (P i) (P j)) ∧ (⋃ i : I, P i) = Set.univ) ↔
        ∃! Q : I → Set (PrimeSpectrum A),
          (∀ i : I, IsClopen (Q i)) ∧
          Pairwise (fun i j : I ↦ Disjoint (Q i) (Q j)) ∧
          (⋃ i : I, Q i) = Set.univ ∧
          ∀ i : I, (Subtype.val : closedPoints (PrimeSpectrum A) → PrimeSpectrum A) ⁻¹'
            Q i = P i) ∧
      (∀ (E : Set (closedPoints (PrimeSpectrum A))), IsClopen E →
        ∀ (O : Set (PrimeSpectrum A)), IsOpen O → Subtype.val '' E ⊆ O →
          ∀ c ∈ E, connectedComponent (c : PrimeSpectrum A) ⊆ O)) := by
  sorry

end PrimeSpectrum
