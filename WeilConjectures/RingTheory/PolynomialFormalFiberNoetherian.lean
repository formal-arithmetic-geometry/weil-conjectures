/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.Algebra.Polynomial.Basic
public import WeilConjectures.RingTheory.GRing
import Mathlib.RingTheory.Polynomial.Basic
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.RingTheory.FibreRingNoetherian

/-!
# Noetherianity of polynomial formal fibres

The formal fibres of `A[X]_q` over a complete local Noetherian domain `A` are Noetherian.

## Implementation details

The completion of the Noetherian local ring `A[X]_q` is Noetherian, and fibres of a Noetherian
ring are Noetherian.

## References

* [Stacks, Tag 07PU]
-/

@[expose] public section
universe u
namespace Polynomial

/-- The formal fibre of `A[X]_q` at a prime, over a complete local Noetherian domain `A`, is
Noetherian. -/
theorem formalFiber_isNoetherian (A : Type u) [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (p : ℕ) (_hp : p.Prime) [CharP (Localization.AtPrime (⊥ : Ideal A)) p]
    (q : Ideal (Polynomial A)) [q.IsMaximal]
    (_hq : q.comap (Polynomial.C : A →+* Polynomial A) = IsLocalRing.maximalIdeal A)
    (r : Ideal (Polynomial A)) [r.IsPrime] (_hrq : r ≤ q) (_hr : r ≠ ⊥)
    (_hrA : r.comap (Polynomial.C : A →+* Polynomial A) = ⊥) :
    let C := AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
      (Localization.AtPrime q)
    IsNoetherianRing (r.Fiber C) := by
  have : IsNoetherianRing (Localization.AtPrime q) := inferInstance
  have : IsNoetherianRing
      (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
        (Localization.AtPrime q)) := AdicCompletion.isNoetherianRing _
  exact Ideal.isNoetherianRing_fiber r
end Polynomial
