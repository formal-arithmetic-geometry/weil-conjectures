/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Semicontinuity.Basic

/-! # Upper semicontinuity of fibre homology of finite free complexes

Source: Stacks Project, Derived Categories of Schemes, Lemma jump-loci, Tag 0BDI,
`literature/stacks-project/perfect.tex` (affine finite-free specialization).
(blueprint: lem-sc-finite-free-complex-homology-upper-semicontinuous).
-/

@[expose] public section

universe u v

open CategoryTheory

namespace ModuleCat

/-- For a bounded complex of finite free modules over a commutative ring, the dimension of
its homology after extension to each residue field is upper semicontinuous. Every integer
strict sublevel set is a finite union of principal opens, hence open and quasi-compact.

Source: Stacks Project, Derived Categories of Schemes, Lemma jump-loci, Tag 0BDI,
`literature/stacks-project/perfect.tex` (affine finite-free specialization).
(blueprint: lem-sc-finite-free-complex-homology-upper-semicontinuous).

Proof (the three steps of the node):
1. Choose finite bases in degrees `i - 1`, `i`, and `i + 1`. Write the adjacent
   differentials as matrices, with fibre ranks `r₀` and `r₁` (def-weil-matrix-rank).
   Rank-nullity for the outgoing differential, and then for the quotient of its kernel
   by the incoming image (lem-weil-pbc-idempotent-charpoly-rank-nullity), gives the fibre
   homology dimension `c - r₁ - r₀`, where `c` is the rank of the middle term.
2. The locus where a matrix has fibre rank at least `s` is the finite union of `D(Δ)`
   for its `s` by `s` minors (def-weil-matrix-rank). Laplace expansion gives the criterion
   using minors of exactly size `s`; the size-zero minor is `1`. Determinants commute
   with reduction to the residue field, and their reductions are nonzero exactly outside
   the prime. Intersections remain finite unions because `D(f) ∩ D(g) = D(fg)`.
3. For an integer threshold `r`, the inequality on the homology dimension is equivalent
   to `r₁ + r₀ > c - r`, with this comparison made in the integers. Both matrix ranks
   are bounded. Thus the sublevel set is the finite union over bounded pairs `(a, b)`
   satisfying `a + b > c - r` of the intersections of the loci `r₁ ≥ a` and `r₀ ≥ b`.
   Step 2 makes this a finite union of principal opens. Principal opens are open and
   quasi-compact, so these sublevel sets are open and quasi-compact and the dimension
   function is upper semicontinuous. -/
theorem finiteFreeComplex_homology_upperSemicontinuous
    (A : Type u) [CommRing A] (K : CochainComplex (ModuleCat.{max u v} A) ℤ)
    (hbounded : ∃ a b : ℤ, K.IsStrictlyGE a ∧ K.IsStrictlyLE b)
    (hfree : ∀ n : ℤ, Module.Free A (K.X n) ∧ Module.Finite A (K.X n)) (i : ℤ) :
    ∃ β : PrimeSpectrum A → ℕ,
      (∀ p : PrimeSpectrum A,
        β p = Module.finrank p.asIdeal.ResidueField
          ((((ModuleCat.extendScalars.{u, u, max u v}
            (algebraMap A p.asIdeal.ResidueField)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K).homology i)) ∧
      UpperSemicontinuous β ∧
      (∀ r : ℤ, ∃ s : Finset A,
        {p : PrimeSpectrum A | (β p : ℤ) < r} =
          ⋃ f ∈ (s : Set A), (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum A))) ∧
      (∀ r : ℤ, IsOpen {p : PrimeSpectrum A | (β p : ℤ) < r} ∧
        IsCompact {p : PrimeSpectrum A | (β p : ℤ) < r}) := by
  sorry

end ModuleCat
