/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.Mathlib.RingTheory.Etale.QuasiFinite
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.Mathlib.RingTheory.Invariant.Profinite

/-!
# Normal local domains with separably closed fraction field are strictly henselian

Let `A` be an integrally closed local domain whose fraction field `Ω` is separably closed (for
instance the localization at a maximal ideal of the integral closure of a domain in a separable
closure of its fraction field). Then `A` is strictly henselian
(`IsStrictlyHenselianLocalRing.of_isFractionRing_of_isSepClosed`).

This is `HenselianLocalRing.of_isSepClosed_fractionRing` together with
`IsLocalRing.isSepClosed_residueField_of_isSepClosed_fractionRing`.
-/

@[expose] public section

open IsLocalRing

namespace IsStrictlyHenselianLocalRing

variable {A : Type*} [CommRing A] [IsLocalRing A] [IsIntegrallyClosed A]

/-- An integrally closed local domain whose fraction field is separably closed is strictly
henselian. -/
theorem of_isFractionRing_of_isSepClosed (Ω : Type*) [Field Ω] [IsSepClosed Ω] [Algebra A Ω]
    [IsFractionRing A Ω] : IsStrictlyHenselianLocalRing A :=
  have := HenselianLocalRing.of_isSepClosed_fractionRing (A := A) Ω
  ⟨IsLocalRing.isSepClosed_residueField_of_isSepClosed_fractionRing Ω⟩

end IsStrictlyHenselianLocalRing

namespace Ideal

variable {R Ω : Type*} [CommRing R] [Field Ω] [Algebra R Ω]
  (Q : Ideal (integralClosure R Ω)) [Q.IsPrime]

section StrictlyHenselian

variable [IsSepClosed Ω] [Algebra.IsAlgebraic R Ω]

end StrictlyHenselian

section Action

open scoped Pointwise

variable {G : Type*} [Group G] [MulSemiringAction G Ω] [SMulCommClass G R Ω]

end Action

section Galois

open scoped Pointwise

variable {K : Type*} [Field K] [Algebra R K] [Algebra K Ω] [IsScalarTower R K Ω] [IsGalois K Ω]
  [IsIntegrallyClosedIn R K] (P : Ideal R) [Q.IsMaximal] [Q.LiesOver P]

end Galois

end Ideal
