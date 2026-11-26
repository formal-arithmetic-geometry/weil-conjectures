/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import WeilConjectures.RingTheory.GRing
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.Polynomial.Basic
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.RingTheory.FibreRingNoetherian
import WeilConjectures.RingTheory.PowerSeriesPolynomialFormalFiberGeometricComponent

/-!
# Generic formal fibres of polynomial rings over power series fields

In positive characteristic the generic formal fibre of a polynomial ring over a finite variable
power series field is Noetherian and geometrically regular.

## Implementation details

`(⊥ : Ideal A).ResidueField` is `κ(0)`, the fraction field of the domain `A`. `Ideal.Fiber`
places `κ(0)` first in the tensor product, canonically exchanging the factors of the completion
`Â ⊗_A K` used in the source.

## References

* [Stacks, Tag 07PR]
-/

@[expose] public section

universe u

namespace MvPowerSeries

/-- In positive characteristic the generic formal fibre of a polynomial ring over a finite
variable power series field is Noetherian and geometrically regular. -/
theorem formalFiber_polynomial_isGeometricallyRegular
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (n m : ℕ)
    (q : Ideal (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k))) [q.IsPrime] :
    let A := MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)
    let C := AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
      (Localization.AtPrime q)
    IsNoetherianRing ((⊥ : Ideal A).Fiber C) ∧
      Algebra.IsGeometricallyRegular (⊥ : Ideal A).ResidueField ((⊥ : Ideal A).Fiber C) := by
  dsimp
  let R := Localization.AtPrime q
  let I := IsLocalRing.maximalIdeal R
  let C := AdicCompletion I R
  let : IsNoetherianRing R := inferInstance
  let : IsNoetherianRing C := AdicCompletion.isNoetherianRing I
  have hnoeth := Ideal.isNoetherianRing_fiber (B := C)
    (⊥ : Ideal (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)))
  exact ⟨hnoeth, hnoeth, formalFiber_polynomial_geometricComponent k p n m q⟩

end MvPowerSeries
