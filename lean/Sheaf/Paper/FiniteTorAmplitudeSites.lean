/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude

/-! # The finite-Tor constructible categories in the two site presentations

Source: Weil conjectures blueprint, sec-smooth-purity/sk-def-sf-operations,
order 1464 (blueprint: def-weil-finite-tor-amplitude).

This module supplies the ordinary-etale presentation using the recorded finite-value
constructibility and Tor-amplitude conventions. The recorded pro-etale, integral and
field-stage definitions remain unchanged in `Sheaf.Paper.FiniteTorAmplitude`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace WeilConjectures

/-- The etale presentation of `Dᵇ_ctf(Y,A_{E,n})`, using the same quotient ring,
with its canonical universe lift, and the recorded etale constructibility convention.
Source: blueprint order 1464 (blueprint: def-weil-finite-tor-amplitude). -/
noncomputable def finiteTorConstructibleEtale
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n) (Y : Scheme.{u}) :
    ObjectProperty (Etale.DerivedCategoryModule
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) Y) :=
  letI : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n hn
  Etale.DerivedCategory.isBoundedConstructible
    (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) Y ⊓
    fun K ↦ ∃ a b : ℤ, a ≤ b ∧ Etale.DerivedCategory.hasTorAmplitudeIn
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) Y a b K

end WeilConjectures
