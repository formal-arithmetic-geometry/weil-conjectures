/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q54
-/
module

public import Sheaf.RingTheory.CompleteIntersectionLocalAlgebra
public import Sheaf.RingTheory.PresentationFittingIdeal
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.SetTheory.Cardinal.ToNat
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Sheaf.TraceFormula.CILocalRingPrincipalNeighbourhood
import WeilConjectures.RingTheory.CompleteIntersectionOverField
import WeilConjectures.AlgebraicGeometry.GlobalCompleteIntersectionEquidimensional
import WeilConjectures.RingTheory.DimensionAtPointLocalRingTrdeg
import Mathlib.RingTheory.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.AlgebraicGeometry.Modules.Differentials
import Sheaf.AlgebraicGeometry.DthFittingSmoothLocus
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.Spectrum.Prime.Topology
import WeilConjectures.RingTheory.Flat.LocalizationPreservesFlatness
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Etale.Kaehler

/-!
# Local complete-intersection smoothing with a Fitting bound

Source: Stacks Project, Examples of Deformation Problems, Tag 0E7X,
lemma-smoothing-at-lci-point (blueprint: lem-sfb-lci-local-fitting-smoothing).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Algebra

/-- A complete-intersection local algebra has a flat, essentially finite type local
`k[[t]]`-deformation whose differential Fitting ideal contains a power of `t`.
Source: Stacks Project, Examples of Deformation Problems, Tag 0E7X,
lemma-smoothing-at-lci-point (blueprint: lem-sfb-lci-local-fitting-smoothing).

The Krull dimension and the residue-field transcendence degree are finite natural
numbers under the hypotheses. `ENat.toNat` after `WithBot.unbotD 0`, and `Cardinal.toNat`,
respectively extract these numbers. The finite free generating surjection `π` computes
exactly the presentation-independent Fitting ideal of
`lem-trf-fitting-ideal-independence-base-change`. The compatible `k`-algebra structure
on `B` is the one induced by `k → k[[t]] → B`.

Proof plan, following the node's nine steps:
1. Write `A` as a prime localization of a finite type `k`-algebra, using essential
   finite type and the fact that every element outside the maximal ideal is a unit.
2. Apply `lem-trf-ci-local-ring-principal-neighbourhood` to obtain a global complete
   intersection `P` with a prime `p` and `P_p ≃ₐ[k] A`.
3. Choose a global complete-intersection presentation with `N` variables and `c`
   equations. By `lem-weil-pbc-global-complete-intersection-equidimensional` and
   `lem-weil-pbc-dimension-at-point-local-ring-trdeg`, `dim P = N-c = d`.
4. Apply `lem-sfb-affine-global-ci-smoothing` to get a finitely presented flat
   `k[[t]]`-algebra `Q`, special fibre `P`, smooth generic fibre, and pure geometric
   fibre dimension `d`.
5. The differentials of the `N` polynomial generators generate `Ω[Q⁄k[[t]]]`,
   by the Leibniz rule. Take its d-th presentation Fitting ideal `I`.
6. Apply `lem-trf-dth-fitting-smooth-locus`, using flatness, finite presentation,
   and pure geometric fibres. Smoothness over `D(t)` implies `V(I) ⊆ V(t)`.
7. The radical/intersection-of-primes formula of
   `lem-weil-pbc-zero-locus-eq-iff-radical-eq` gives `t ∈ radical I`, hence `t^e ∈ I`
   for a positive, in particular nonnegative, integer `e`.
8. Let `q` be the inverse image of `p` and put `B = Q_q`. Localization preserves
   flatness by `lem-pc-affine-flat-module-localization-preserves-flatness`, and
   `lem-weil-pbc-localization-at-prime-of-quotient` identifies `B/tB` with `A`.
   The fraction maps fix `k`, so this is an isomorphism of `k`-algebras.
9. By `lem-weil-pbc-kahler-differentials-localization` the differential module
   localizes. Tensoring its finite free surjection gives `π`; Fitting base change
   and presentation independence in `lem-trf-fitting-ideal-independence-base-change`
   carry the parameter-power bound from `Q` to `B`.
-/
theorem exists_local_fitting_smoothing
    (k : Type u) [Field k] (A : Type v) [CommRing A] [Algebra k A] [IsLocalRing A]
    (hA : IsCompleteIntersectionLocalAlgebra k A) :
    ∃ (e : ℕ) (B : Type (max u v)) (_ : CommRing B) (_ : IsLocalRing B)
      (_ : Algebra (PowerSeries k) B) (_ : Algebra k B)
      (_ : IsScalarTower k (PowerSeries k) B),
      Module.Flat (PowerSeries k) B ∧ EssFiniteType (PowerSeries k) B ∧
      Nonempty ((B ⧸ Ideal.span
        ({algebraMap (PowerSeries k) B PowerSeries.X} : Set B)) ≃ₐ[k] A) ∧
      ∃ (n : ℕ) (π : (Fin n → B) →ₗ[B] KaehlerDifferential (PowerSeries k) B),
        Function.Surjective π ∧
        (algebraMap (PowerSeries k) B PowerSeries.X) ^ e ∈
          π.presentationFittingIdeal
            ((WithBot.unbotD 0 (ringKrullDim A)).toNat +
              (Algebra.trdeg k (IsLocalRing.ResidueField A)).toNat) := by
  sorry

end Algebra
