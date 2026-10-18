/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q17
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Generic basis subtraction and the relative flat locus

Source: Stacks Project, Tag 05I3, `flat.tex`, Lemma `lemma-induction-step`, localized over
all base primes; Tag 05CL, `algebra.tex`, Lemma `lemma-universally-injective-check-stalks`.
(blueprint: lem-trf-free-subtraction-flatness)

A localization at an A-prime q over an R-prime p has its canonical R_p-module structure.
For this module, flatness over R_p is equivalent to flatness over R, by
`Module.flat_iff_of_isLocalization`. We use the latter formulation, with exactly the
same localized module, both in the generic-point hypothesis and the flat-locus conclusion.
The fibre ring is written with the residue field on the left; tensor symmetry identifies
it with A tensor_R kappa(p).
-/

@[expose] public section

universe u v w

open AlgebraicGeometry TensorProduct

namespace Module

/-- Generic basis subtraction (Stacks, Tag 05I3 and Tag 05CL).
(blueprint: lem-trf-free-subtraction-flatness)

The family `ξ` consists of the inverse images of the zero ideals in the fibre rings;
`hξ` specifies these primes uniquely. Geometric integrality guarantees that these
kernels are prime. `hgenericFlat` is flatness at these generic points, equivalently over
R_p. The map `α` becomes an isomorphism over each kappa(ξ(p)), as stated by `hgenericBasis`.
The cokernel is the actual quotient `N ⧸ LinearMap.range α`.

Proof: (1) Fix a base prime p and localize to R_p. Flatness, finite presentation, and
geometric integrality survive this base change. Apply
`lem-trf-local-generic-basis-universal-injective` (05I3) at the generic prime ξ(p):
`hgenericFlat` and `hgenericBasis` give universal injectivity of the base-localized map.
(2) Further localization at any q above p preserves this injectivity after tensoring
with any R_p-module, since localization is exact. Apply
`lem-trf-universal-injective-check-stalks` (05CL) to deduce global universal injectivity.
(3) If N_q is R_p-flat, apply the same local 05I3 criterion at q to get flatness of the
localized cokernel. Conversely, the localized source is R_p-flat because A is R-flat.
Universal injectivity and right exactness of tensor give a short exact row after every
tensor product. For an injection L' to L, an element of L' tensor N_q killed below first
lifts from L' tensor A_q^r by flatness of the cokernel; its lift is zero by injectivity
of the lower row and flatness of A_q^r. Thus N_q is flat (the flat-extension argument
of Algebra, Lemma `lemma-flat-ses`, Tag 00HM). Convert between R and R_p-flatness using
`Module.flat_iff_of_isLocalization` throughout. -/
theorem free_subtraction_flatness
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] [Algebra.FinitePresentation R A]
    [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap R A)))]
    (N : Type v) [AddCommGroup N] [Module A N] [Module R N] [IsScalarTower R A N]
    [Module.Finite A N] (r : ℕ) (α : (Fin r → A) →ₗ[A] N)
    (ξ : PrimeSpectrum R → PrimeSpectrum A)
    (hξ : ∀ p : PrimeSpectrum R,
      (ξ p).asIdeal = RingHom.ker
        (Algebra.TensorProduct.includeRight : A →ₐ[R] p.asIdeal.ResidueField ⊗[R] A))
    (hgenericFlat : ∀ p : PrimeSpectrum R,
      Module.Flat R (LocalizedModule (ξ p).asIdeal.primeCompl N))
    (hgenericBasis : ∀ p : PrimeSpectrum R,
      Function.Bijective (α.baseChange (ξ p).asIdeal.ResidueField)) :
    (∀ (L : Type (max u w)) [AddCommGroup L] [Module R L],
      Function.Injective ((α.restrictScalars R).lTensor L)) ∧
    ∀ q : PrimeSpectrum A,
      Module.Flat R (LocalizedModule q.asIdeal.primeCompl N) ↔
        Module.Flat R (LocalizedModule q.asIdeal.primeCompl (N ⧸ LinearMap.range α)) := by
  sorry

end Module
