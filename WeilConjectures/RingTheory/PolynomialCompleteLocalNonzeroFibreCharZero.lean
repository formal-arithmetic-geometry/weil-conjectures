/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import WeilConjectures.RingTheory.GRing
import WeilConjectures.RingTheory.PolynomialRegularBaseFormalFibre
import WeilConjectures.RingTheory.PolynomialCompleteLocalNonzeroFibreCharZeroReduction

/-!
# Nonzero polynomial formal fibres in characteristic zero

For a complete local domain `A` of characteristic zero, the formal fibres of `A[X]_q` over nonzero
primes lying over zero are geometrically regular.

## Implementation details

After reducing to a regular complete local subring `A₀` (Tags 032D, 07PP), the fibre is `R / f R`
for a regular ring `R` and an irreducible `f`. The derivation `d/dX` extends to `R` (Tag 07PE),
and `f'` is a unit modulo `f` in characteristic zero, so `R / f R` is regular (Tag 07PF).

## References

* [Stacks, Tag 07PV] (paragraph 4 of the proof)
* [Stacks, Tag 07PU] (second paragraph of the proof)
* [Stacks, Tag 032D]
* [Stacks, Tag 07PP]
* [Stacks, Tag 07NF]
* [Stacks, Tag 07NY]
* [Stacks, Tag 07PE]
* [Stacks, Tag 07PF]
-/

@[expose] public section

universe u

namespace Polynomial

/-- In characteristic zero, the formal fibre of `A[X]_q` over a nonzero prime lying over zero is
geometrically regular, for a complete local domain `A`. -/
theorem completeLocalNonzeroFibreCharZero
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (q : Ideal (Polynomial A)) [q.IsMaximal]
    (hq : q.comap (Polynomial.C : A →+* Polynomial A) = IsLocalRing.maximalIdeal A)
    [CharZero (Localization.AtPrime (⊥ : Ideal A))]
    (r : Ideal (Polynomial A)) [r.IsPrime] (hrq : r ≤ q) (hr : r ≠ ⊥)
    (hrA : r.comap (Polynomial.C : A →+* Polynomial A) = ⊥) :
    Algebra.IsGeometricallyRegular r.ResidueField
      (r.Fiber (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
        (Localization.AtPrime q))) := by
  obtain ⟨A₀, hA₀, hdom, hnoeth, hreg, hchar, hlocal, hcomplete, q₀, r₀,
    hq₀max, hr₀prime, hq₀, hr₀q₀, hr₀, hr₀A, htransfer⟩ :=
    completeLocalNonzeroFibreCharZero_reduction A q hq r hrq hr hrA
  let _ := hdom
  let _ := hnoeth
  let _ := hreg
  let _ := hchar
  let _ := hlocal
  let _ := hcomplete
  let _ := hq₀max
  let _ := hr₀prime
  exact htransfer (regularBase_formalFibre_isRegular A₀ q₀ hq₀ r₀ hr₀q₀ hr₀A)

end Polynomial
