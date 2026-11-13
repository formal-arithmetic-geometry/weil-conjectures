/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.QuasiFiniteOverPolynomialAlgebra
import WeilConjectures.AlgebraicGeometry.FibreDimensionBoundedOpenUpstairsAux

/-!
# Fibre dimension is bounded on a neighbourhood

## References

* [Stacks Project, Tag 00QH](https://stacks.math.columbia.edu/tag/00QH)
-/

@[expose] public section

universe u v

namespace Algebra

/-- For a finite type ring map `R → S` and a prime `q` of `S` at which the fibre
`κ(p) ⊗[R] S` (`p` the contracted prime) has local dimension `d`, there is an open
neighbourhood `V` of `q` in `Spec S` such that every prime `q' ∈ V` has local fibre
dimension at most `d` (Stacks, Tag 00QH). -/
theorem fibre_dimension_bounded_open_upstairs
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [FiniteType R S] (q : PrimeSpectrum S) (d : ℕ) :
    topologicalKrullDimAt
        (PrimeSpectrum.preimageEquivFiber R S (PrimeSpectrum.comap (algebraMap R S) q)
          ⟨q, rfl⟩) = (d : WithBot ℕ∞) →
      ∃ V : Set (PrimeSpectrum S), IsOpen V ∧ q ∈ V ∧
        ∀ q' ∈ V,
          topologicalKrullDimAt
              (PrimeSpectrum.preimageEquivFiber R S (PrimeSpectrum.comap (algebraMap R S) q')
                ⟨q', rfl⟩) ≤ (d : WithBot ℕ∞) := by
  intro hdim
  obtain ⟨g, hg, f, hft, hq⟩ :=
    exists_quasiFinite_over_polynomial_algebra R S q d hdim
  refine ⟨(PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S)),
    PrimeSpectrum.isOpen_basicOpen, ?_, ?_⟩
  · exact (PrimeSpectrum.mem_basicOpen g q).2 hg
  · intro q' hq'
    exact fibre_dimension_le_of_quasiFinite_polynomial_localization
      g d f hft hq q' ((PrimeSpectrum.mem_basicOpen g q').1 hq')

end Algebra
