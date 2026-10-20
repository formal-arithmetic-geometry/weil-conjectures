module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.RingTheory.Depth

import WeilConjectures.AlgebraicGeometry.FibreCohenMacaulayLocus
import WeilConjectures.RingTheory.DepthLeDimAssociatedPrime
import Sheaf.TraceFormula.MinimalPrimesDenseSpectrum

/-! # Dense Cohen--Macaulay locus for a finite type algebra over a field

Source: Stacks Project, Algebra, Tag 00RG, label lemma-generic-CM (using Tag 00RF).
(blueprint: lem-trf-generic-cm-locus-field)
-/

@[expose] public section

set_option autoImplicit false

universe u v

open Topology

/-- The Cohen--Macaulay locus of a finite type algebra over a field is dense and open.
Source: Stacks Project, Algebra, Tag 00RG, label lemma-generic-CM (using Tag 00RF).
(blueprint: lem-trf-generic-cm-locus-field)

Proof: The finite type algebra over the field is finitely presented and flat over the
field, so the general fibre Cohen--Macaulay-locus openness theorem applies to its
spectrum. A minimal prime localizes to a zero-dimensional Noetherian local ring;
the associated-prime depth bound and the empty regular sequence identify its depth
with its dimension. Minimal primes are dense in the spectrum, so the displayed
locus is dense. The localization, affine-stalk, finite-type Noetherian and
finite-presentation results, together with the prime-localization correspondence,
are used as recorded in the node proof dependencies.
-/
theorem generic_cm_locus_field
    (k : Type u) [Field k] (A : Type v) [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] :
    IsOpen {q : PrimeSpectrum A |
      IsNoetherianRing (Localization.AtPrime q.asIdeal) ∧
        (IsLocalRing.depth (R := Localization.AtPrime q.asIdeal)
          (Localization.AtPrime q.asIdeal) : WithBot ℕ∞) =
          ringKrullDim (Localization.AtPrime q.asIdeal)} ∧
      Dense {q : PrimeSpectrum A |
        IsNoetherianRing (Localization.AtPrime q.asIdeal) ∧
          (IsLocalRing.depth (R := Localization.AtPrime q.asIdeal)
            (Localization.AtPrime q.asIdeal) : WithBot ℕ∞) =
            ringKrullDim (Localization.AtPrime q.asIdeal)} ∧
      ∀ V : Set (PrimeSpectrum A), IsOpen V → V.Nonempty →
        ∃ q : PrimeSpectrum A, q ∈ V ∧
          IsNoetherianRing (Localization.AtPrime q.asIdeal) ∧
            (IsLocalRing.depth (R := Localization.AtPrime q.asIdeal)
              (Localization.AtPrime q.asIdeal) : WithBot ℕ∞) =
              ringKrullDim (Localization.AtPrime q.asIdeal) := by
  sorry

end
