/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Polynomial.Basic
public import WeilConjectures.RingTheory.GRing
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.RingTheory.CompletionFiniteExtension
import WeilConjectures.RingTheory.Derivation.CompletionAndLocalization
import WeilConjectures.RingTheory.FibreRingNoetherian
import WeilConjectures.RingTheory.FiniteOverCompleteLocalProduct
import WeilConjectures.RingTheory.FormallySmoothAdic
import WeilConjectures.RingTheory.FormallySmoothCompleteLocalRegular
import WeilConjectures.RingTheory.HypersurfaceDerivationRegular
import WeilConjectures.RingTheory.LocalizationPrimeResidueFieldIso
import WeilConjectures.RingTheory.PolynomialLocalCompletionFormallySmooth
import WeilConjectures.RingTheory.PolynomialFormalFiberNoetherian
import WeilConjectures.RingTheory.PolynomialFormalFiberGeometric

/-!
# Formal fibres of a polynomial ring over a complete local domain

For a complete local domain `A` and a maximal ideal `q` of `A[X]` over the maximal ideal of `A`,
the formal fibres of `A[X]_q` at nonzero primes above zero are Noetherian and geometrically
regular.

## Implementation details

The fibre uses Mathlib's residue-field-first tensor order, canonically isomorphic to
`C ⊗ κ(r)`. Completion is at the maximal ideal of the localization, which is `q A[X]_q`. The
characteristic hypothesis is retained as in the source, although the proof does not use it.

## References

* [Stacks, Tag 07PU]
-/

@[expose] public section

universe u

namespace Polynomial

/-- The formal fibre of `A[X]_q` at a nonzero prime above zero, over a complete local domain `A`,
is Noetherian and geometrically regular. -/
theorem formalFiber_isGeometricallyRegular (A : Type u) [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (p : ℕ) (hp : p.Prime) [CharP (Localization.AtPrime (⊥ : Ideal A)) p]
    (q : Ideal (Polynomial A)) [q.IsMaximal]
    (hq : q.comap (Polynomial.C : A →+* Polynomial A) = IsLocalRing.maximalIdeal A)
    (r : Ideal (Polynomial A)) [r.IsPrime] (hrq : r ≤ q) (hr : r ≠ ⊥)
    (hrA : r.comap (Polynomial.C : A →+* Polynomial A) = ⊥) :
    let C := AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
      (Localization.AtPrime q)
    IsNoetherianRing (r.Fiber C) ∧ Algebra.IsGeometricallyRegular r.ResidueField (r.Fiber C) := by
  exact ⟨formalFiber_isNoetherian A p hp q hq r hrq hr hrA,
    formalFiber_isGeometricallyRegular_component A p hp q hq r hrq hr hrA⟩

end Polynomial
