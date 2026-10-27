module

public import Mathlib.Data.Complex.Basic
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

import WeilConjectures.RingTheory.IntegerPrimeLocalizations
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import WeilConjectures.RingTheory.LocalizationPrimeResidueFieldIso
import Sheaf.AlgebraicGeometry.UnitBinomialFiniteEtale
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.AlgebraicGeometry.AffineScheme
import Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Spectrum.Prime.Topology
import WeilConjectures.AlgebraicGeometry.NormalSectionsFiniteProduct
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.DedekindDomain.Dvr

/-!
# Prime localizations of tame cyclotomic integer rings

Source: Stacks Project, More on Algebra, Tag 0AP2, applied to the cyclotomic
coefficient ring of Travaux de Gabber, Expose X, 1.2--1.3
(blueprint: lem-per-cyclotomic-local-ring-dvr).

The subring `Subring.closure { (N : ℂ)⁻¹, ζ }` is exactly `ℤ[1/N, ζ]`:
a unital subring already contains every integer.
-/

@[expose] public section

set_option autoImplicit false

namespace IsPrimitiveRoot

/-- Every prime localization of `ℤ[1/N, ζ]` is a field or a discrete valuation ring.

Source: Stacks Project, More on Algebra, Tag 0AP2, and Travaux de Gabber,
Expose X, 1.2--1.3 (blueprint: lem-per-cyclotomic-local-ring-dvr).

Proof plan:
1. Write `R = ℤ[1/N]`. IntegerPrimeLocalizations, localization Noetherianity,
   localization normality and the prime correspondence show that `R` is a
   Noetherian normal domain of dimension at most one.
2. The unit-binomial finite-etale theorem makes `B = R[T]/(T^N - 1)` finite free
   and etale over `R`. Evaluation at `ζ` surjects onto the actual subring
   `A = ℤ[1/N, ζ]`, so both `B` and `A` are finite over `R` and Noetherian.
3. Affine stalks of `Spec R` are normal domains by localization normality.
   Etale implies smooth; smooth normality ascent gives normal domain stalks
   on `Spec B` (the as-yet-unstated node lem-sfb-smooth-normal-ascent).
4. The quasi-compact locally Noetherian normal-sections finite-product theorem
   identifies `B` with a finite product of normal domains `Dᵢ`. Each `Dᵢ` is
   finite over `R`, by projecting the finite generating family of `B`.
5. Evaluation into the nonzero domain `A ⊆ ℂ` sends exactly one coordinate
   idempotent to one and all others to zero. Thus it factors through a
   surjection `h : Dᵢ → A` from one normal domain factor.
6. The composite `R → Dᵢ → A` is injective. Both zero and the prime kernel of
   `h` contract to zero in `R`. Finiteness implies integrality, so integral
   incomparability makes this kernel zero. Hence `A` is a normal domain.
7. Integrality and incomparability bound the dimension of `A` by one. A
   nonzero prime is maximal and forces dimension one. The Dedekind-domain
   localization theorem then makes its localization a DVR.
8. At the zero prime every nonzero element is inverted. A nonzero fraction
   `a/s` has inverse `s/a`; the localization is therefore a field.
-/
theorem cyclotomic_prime_localization_isField_or_isDiscreteValuationRing
    (N : ℕ) (hN : 1 ≤ N) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ N)
    (p : Ideal (Subring.closure ({(N : ℂ)⁻¹, ζ} : Set ℂ))) [p.IsPrime] :
    IsField (Localization.AtPrime p) ∨ IsDiscreteValuationRing (Localization.AtPrime p) := by
  sorry

end IsPrimitiveRoot
