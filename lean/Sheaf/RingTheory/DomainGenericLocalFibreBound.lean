/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import WeilConjectures.Mathlib.Topology.KrullDimension
import Mathlib.RingTheory.Localization.BaseChange
import WeilConjectures.RingTheory.FiniteTypeDomainDimensionTrdeg
import WeilConjectures.RingTheory.DimensionAtPointComponents
import WeilConjectures.AlgebraicGeometry.FibreDimensionBoundedOpenUpstairs
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Generic dimension bounds local dimensions of residue-field fibres

Source: literature/stacks-project/algebra.tex, Tag 00QK, first dimension inequality,
using Tag 00QH; this inequality only needs an integral domain base.
(blueprint: lem-trf-domain-generic-local-fibre-bound).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open scoped TensorProduct

namespace Algebra

/-- The generic fibre of a finite type domain containing an integral domain `A` is a
nonzero finite type domain. Its dimension is a finite integer `d`, equal to the
transcendence degree of its fraction field and to its local topological dimension at
all primes. Every residue-field fibre is finite type, and its local topological
dimensions are finite integers at least `d`.

The tensor factors follow Mathlib's convention: the field is on the left. The
canonical tensor-factor swap identifies these rings, as algebras over the field,
with `D ⊗[A] K` and `D ⊗[A] κ(p)` in the source.

Source: literature/stacks-project/algebra.tex, Tag 00QK, first inequality, and Tag 00QH.
(blueprint: lem-trf-domain-generic-local-fibre-bound).

Proof:
1. Finite algebra generators of `D` tensor to generators of each field fibre.
   By lem-weil-pbc-generic-fibre-localization-domain-irreducible, the generic fibre
   is the localization of `D` at the nonzero elements of `A`, after swapping tensor
   factors. It is a nonzero domain, and `D` injects into it: a fraction `z/1` is zero
   only if `az = 0` for a nonzero `a` from `A`, hence `z = 0`.
2. Apply lem-weil-pbc-finite-type-domain-dimension-trdeg to the generic fibre to
   obtain a finite dimension `d` equal to its fraction field's transcendence degree.
   By lem-weil-pbc-dimension-at-point-components, its local dimension at any prime
   equals `d`, since a domain has just the minimal prime `(0)`.
3. At a prime `Q` of a residue-field fibre, the same component formula gives a finite
   nonnegative local dimension `n`. By lem-weil-pbc-fibre-ring-primes-bijection, `Q`
   corresponds to a prime `q` of `D` and is the canonical fibre point over `q`.
4. By lem-weil-pbc-fibre-dimension-bounded-open-upstairs there is an open neighbourhood
   of `q` on which local fibre dimensions are at most `n`. By
   lem-weil-pbc-spec-localization-away-basic-open, choose a basic open `D(g)` inside
   it containing `q`. Then `g` is nonzero, so the zero prime of `D` also lies in it.
5. The zero prime contracts to zero in `A`. Its residue field is `FractionRing A`,
   and the fibre-prime bijection identifies its fibre point with the zero prime of
   the generic fibre. Step 2 gives local dimension `d` there, so step 4 gives `d ≤ n`.
   A fibre with no primes has no pointwise condition to check.
-/
theorem domain_generic_local_fibre_bound
    {A : Type u} {D : Type v} [CommRing A] [CommRing D] [IsDomain A] [IsDomain D]
    [Algebra A D] (hAD : Function.Injective (algebraMap A D))
    (hft : (algebraMap A D).FiniteType) :
    IsDomain (FractionRing A ⊗[A] D) ∧
    Algebra.FiniteType (FractionRing A) (FractionRing A ⊗[A] D) ∧
    ∃ d : ℕ,
      ringKrullDim (FractionRing A ⊗[A] D) = (d : WithBot ℕ∞) ∧
      Algebra.trdeg (FractionRing A) (FractionRing (FractionRing A ⊗[A] D)) =
        (d : Cardinal) ∧
      (∀ P : PrimeSpectrum (FractionRing A ⊗[A] D),
        topologicalKrullDimAt P = (d : WithBot ℕ∞)) ∧
      ∀ p : PrimeSpectrum A,
        Algebra.FiniteType p.asIdeal.ResidueField (p.asIdeal.Fiber D) ∧
        ∀ Q : PrimeSpectrum (p.asIdeal.Fiber D),
          ∃ n : ℕ, topologicalKrullDimAt Q = (n : WithBot ℕ∞) ∧ d ≤ n := by
  sorry

end Algebra
