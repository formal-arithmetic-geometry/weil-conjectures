/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q19
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Density of minimal primes in an affine spectrum

Source: Stacks Project, `literature/stacks-project/algebra.tex`, Tag 00RG proof,
final sentence (blueprint: lem-trf-minimal-primes-dense-spectrum).
-/

@[expose] public section

universe u v

open AlgebraicGeometry

/-- Minimal-prime points are dense in the spectrum of a finite-type algebra over a field.

Source: Stacks Project, `literature/stacks-project/algebra.tex`, Tag 00RG proof,
final sentence (blueprint: lem-trf-minimal-primes-dense-spectrum).

Proof plan. Given a nonempty open set, choose a point in it. The basic-open basis for
`PrimeSpectrum A` gives an element `f : A` and a basic open `D(f)` containing that point
and contained in the given open. The minimal-prime existence theorem applied to
`⊥ ≤ p.asIdeal` gives a minimal prime `q ≤ p.asIdeal`; since `f ∉ p.asIdeal`, also
`f ∉ q`, so the point defined by `q` lies in `D(f)`. Thus every nonempty open meets
the displayed set, which is the definition of density. -/
theorem minimalPrimes_dense_spectrum
    {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] :
    Dense {p : PrimeSpectrum A | p.asIdeal ∈ minimalPrimes A} := by
  sorry

end
