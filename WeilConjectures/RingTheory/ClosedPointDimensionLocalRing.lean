/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.RingTheory.DimensionAtPointComponents

/-!
# Dimension at a closed point of an affine scheme over a field

The local topological dimension of the spectrum of a finitely generated algebra `S` over a
field at a maximal ideal `m` equals `dim S_m`.

## Implementation details

Chains of primes below `m` give chains of irreducible closed subsets in every neighbourhood of
`m`, which gives the lower bound. For the upper bound, one removes the finitely many
irreducible components not passing through `m`; a chain of irreducible closed subsets in the
resulting neighbourhood lies in a component `V(q)` with `q ⊆ m`, and its length is bounded by
`dim S/q`, which equals the dimension of `S/q` at `m`.

## References

* [Stacks, Tag 00OU], using the proof of [Stacks, Tag 00OT]
-/

@[expose] public section

universe u v

namespace AlgebraicGeometry

/-- The local topological dimension of the spectrum of a finitely generated algebra over a field,
at a maximal ideal, equals the Krull dimension of the localization at that ideal. -/
theorem topologicalKrullDimAt_eq_ringKrullDim_localizationAtMaximal
    {k : Type u} [Field k] {S : Type v} [CommRing S] [Algebra k S]
    (hfg : ∃ (n : ℕ) (f : MvPolynomial (Fin n) k →ₐ[k] S), Function.Surjective f)
    (m : Ideal S) [m.IsMaximal] :
    topologicalKrullDimAt (⟨m, inferInstance⟩ : Spec (CommRingCat.of S)) =
      ringKrullDim (Localization.AtPrime m) := by
  have : Algebra.FiniteType k S := Algebra.FiniteType.iff_quotient_mvPolynomial''.mpr hfg
  obtain ⟨qs, hqs, hne, n, hdim, hcomponents, hattained, hquotients, hquotient,
    hlower, m', hm', hle, hlocal⟩ := dimension_at_point_components (k := k) m
  have hmax : m = m' := Ideal.IsMaximal.eq_of_le inferInstance hm'.ne_top hle
  subst m'
  exact hdim.trans hlocal.symm

end AlgebraicGeometry
