/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q16
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite

/-!
# Chosen compact-support exchange in the published finite coefficient framework

Source: blueprint main-20261015, pur713-def-shriek-exchange-chosen, order 2358
(blueprint: pur713-def-shriek-exchange-chosen).
The comparison is supplied data on the ambient category, exactly as in the source.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-- Postcompose the auxiliary compactification exchange with the specified comparison
into the chosen compactification. No ambient comparison is claimed to exist.
Source: blueprint pur713-def-shriek-exchange-chosen, displayed defining formula
(blueprint: pur713-def-shriek-exchange-chosen). -/
def fixedCompactSupportExchangeChosen (A : Type (u + 1)) [CommRing A]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback g' f' f g) (c : Compactification f) (cf' : Compactification f')
    (theta : Rf_!(c.ofIsPullback sq)[ModuleCat.{u + 1} A] ≅
      Rf_!(cf')[ModuleCat.{u + 1} A]) :
    Rf_!(c)[ModuleCat.{u + 1} A] ⋙ L((g)^*[ModuleCat.{u + 1} A]) ⟶
      L((g')^*[ModuleCat.{u + 1} A]) ⋙ Rf_!(cf')[ModuleCat.{u + 1} A] :=
  rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat.{u + 1} A) sq c ≫
    (Functor.isoWhiskerLeft L((g')^*[ModuleCat.{u + 1} A]) theta).hom

/-- The same postcomposition formula at one object, allowing the canonical comparison
only on that object's etale-origin class. This does not assert any ambient comparison.
Source: blueprint pur713-def-shriek-exchange-chosen, component formula used by
pur9-cs-def-bc (blueprint: pur713-def-shriek-exchange-chosen). -/
def fixedCompactSupportExchangeChosenComponent (A : Type (u + 1)) [CommRing A]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback g' f' f g) (c : Compactification f) (cf' : Compactification f')
    (M : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (theta : (Rf_!(c.ofIsPullback sq)[ModuleCat.{u + 1} A]).obj
        ((L((g')^*[ModuleCat.{u + 1} A])).obj M) ≅
      (Rf_!(cf')[ModuleCat.{u + 1} A]).obj
        ((L((g')^*[ModuleCat.{u + 1} A])).obj M)) :=
  (rightDerivedLowerShriekOfCompactificationBaseChangeMap
    (ModuleCat.{u + 1} A) sq c).app M ≫ theta.hom

/-- The coefficient specialization of the chosen compact-support exchange to exactly
A=O_E/(varpi_E^n), with its standard size lift. All positive levels, including n=1,
are retained. Source: blueprint pur713-def-shriek-exchange-chosen, coefficient convention
and displayed defining formula (blueprint: pur713-def-shriek-exchange-chosen). -/
def finiteFixedCompactSupportExchangeChosen
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (_hn : 1 ≤ n)
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback g' f' f g) (c : Compactification f) (cf' : Compactification f')
    (theta : Rf_!(c.ofIsPullback sq)[ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))] ≅
      Rf_!(cf')[ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))]) :=
  fixedCompactSupportExchangeChosen
    (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) sq c cf' theta

/-- Postcomposition by the comparison preserves and reflects component invertibility.
Source: blueprint pur713-def-shriek-exchange-chosen, final sentence
(blueprint: pur713-def-shriek-exchange-chosen).
Proof: composition with an isomorphism is invertible exactly when its other factor is:
compose with theta inverse in one direction, and with theta in the other. -/
theorem isIso_finiteFixedCompactSupportExchangeChosen_app_iff
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n)
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback g' f' f g) (c : Compactification f) (cf' : Compactification f')
    (theta : Rf_!(c.ofIsPullback sq)[ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))] ≅
      Rf_!(cf')[ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))])
    (M : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))))) :
    IsIso ((finiteFixedCompactSupportExchangeChosen l E n hn sq c cf' theta).app M) ↔
      IsIso ((rightDerivedLowerShriekOfCompactificationBaseChangeMap
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)))
          sq c).app M) := by
  sorry

end AlgebraicGeometry.ProEtale
