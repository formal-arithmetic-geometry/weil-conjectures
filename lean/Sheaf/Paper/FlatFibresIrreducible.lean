/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.Topology.Irreducible

/-! # Flat finite-presentation maps with dense irreducible fibres

Source: Stacks Project, Algebra, Lemma 00I6 (algebra-lemma-flat-fibres-irreducible)
(blueprint: lem-weil-pbc-flat-fibres-irreducible)
-/

@[expose] public section

/--
For a flat finitely presented algebra over an irreducible ring, irreducibility of
fibres over a dense set of primes implies irreducibility of the total spectrum.
Source: Stacks Project, Algebra, Lemma 00I6 (algebra-lemma-flat-fibres-irreducible)
(blueprint: lem-weil-pbc-flat-fibres-irreducible).
Proof: flatness and finite presentation make the induced map
`PrimeSpectrum T → PrimeSpectrum R` open by
`lem-weil-pbc-flat-finite-presentation-open` (Stacks Tag 00I1).
For each prime `p`, its set-theoretic fibre is homeomorphic to the spectrum of
`p.asIdeal.Fiber T` by `lem-weil-pbc-fibre-spec-homeomorphism` (Stacks Tag 00E6).
Thus `hdense` gives irreducible topological fibres over a dense set of primes.
Apply `lem-weil-pbc-irreducible-on-top` (Stacks Tag 004Z) to this open map and
the irreducible base `hR` to obtain irreducibility of the total spectrum.
Nonemptiness follows by choosing a prime in the dense set (the base is nonempty)
and then a point in its nonempty irreducible fibre.
-/
theorem flat_finitePresentation_dense_irreducible_fibres
    {R T : Type*} [CommRing R] [CommRing T] [Algebra R T]
    (hR : IsIrreducible (Set.univ : Set (PrimeSpectrum R)))
    (hflat : (algebraMap R T).Flat)
    (hfp : (algebraMap R T).FinitePresentation)
    (hdense : ∃ U : Set (PrimeSpectrum R), Dense U ∧
      ∀ p ∈ U, IsIrreducible (Set.univ : Set (PrimeSpectrum (p.asIdeal.Fiber T)))) :
    IsIrreducible (Set.univ : Set (PrimeSpectrum T)) := by
  sorry
