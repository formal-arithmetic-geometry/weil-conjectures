/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOpenProper.CondensedOpenProperPasting
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing

/-! Admissible condensed pasting data for the four proper/open coefficients.
Source: the coefficient construction clauses of the normalized condensed proper/open
interchange (blueprint: lem-sf-condensed-proper-open-interchange).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
open AlgebraicGeometry
namespace AlgebraicGeometry.ProEtale.CondensedRing
open CondensedOpenProper

abbrev finiteCoefficient (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type u) [Field E] [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (n : ℕ) : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  letI : TopologicalSpace (Padic.coefficientExtensionRing ℓ E n) := ⊥
  letI : DiscreteTopology (Padic.coefficientExtensionRing ℓ E n) := ⟨rfl⟩
  Profinite.continuousCoefficientRingObj (Padic.coefficientExtensionRing ℓ E n)

abbrev integralCoefficient (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type u) [Field E] [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E] :
    Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  letI : NormedField E := (Padic.coefficientExtensionAbsoluteValue ℓ E).toNormedField
  Profinite.continuousCoefficientRingObj (Padic.coefficientExtensionIntegers ℓ E)

abbrev fieldCoefficient (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type u) [Field E] [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E] :
    Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  letI : NormedField E := (Padic.coefficientExtensionAbsoluteValue ℓ E).toNormedField
  Profinite.continuousCoefficientRingObj E

/-- The four displayed coefficient models supply the normalized condensed pasting package.
The finite quotient conversion uses the finite discrete carrier and the recorded coefficient
extension; the integral and field conversions use the unique extended ell-adic topology; the
algebraic-closure branch is the existing finite-subextension-valued ring. The resulting package
is the exact input needed by the normalized open/proper mate construction.
Source: the coefficient-admissibility step of the proof of
`lem-sf-condensed-proper-open-interchange`.
(blueprint: lem-sf-condensed-proper-open-interchange) -/
theorem condensedProperOpenPastingData
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type u) [Field E] [Algebra (Padic ℓ) E]
    [FiniteDimensional (Padic ℓ) E] (n : ℕ)
    (_hΛ : Nonempty (Mon.mk Λ ≅ Mon.mk (finiteCoefficient ℓ E n)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (integralCoefficient ℓ E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (fieldCoefficient ℓ E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ))) :
    Nonempty (Pasting Λ) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
