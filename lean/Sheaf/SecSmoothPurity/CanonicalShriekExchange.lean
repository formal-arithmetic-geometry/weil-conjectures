/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedExtensionZeroBaseChange
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Sheaf.NumberTheory.Padics.CoefficientExtension
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.Compactification.BaseChange

/-!
# Finite-coefficient compact-support exchange

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
`sk-prop-sp-purity-bc/pur713-def-shriek-exchange.md` (blueprint: pur713-def-shriek-exchange).

The exchange is the canonical compactification composite: proper direct-image base change
followed by the exact open-extension base-change isomorphism.  The construction is on the
full unbounded derived categories and retains the auxiliary base-changed compactification.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-- The finite-coefficient compact-support exchange attached to a chosen compactification.
Source: blueprint node `pur713-def-shriek-exchange`, order 2357
(blueprint: pur713-def-shriek-exchange).

The component at `K` is the proper direct-image base-change mate applied to the
extension-by-zero complex, followed by the canonical open-extension base-change map.
The latter is obtained from `ordinaryOpenExtensionBaseChangeIso`; exactness of all four
inverse-image and open-extension functors identifies their derived maps with the termwise
maps.  No compactification-independence comparison or invertibility assertion is included.
-/
noncomputable def canonicalFiniteCoefficientCompactSupportExchange
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (_hn : 1 ≤ n)
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g)
    (c : Compactification f) :
    Rf_!(c)[ModuleCat.{u + 1} (ULift.{u + 1, u}
      (Padic.coefficientExtensionRing l E n))] ⋙
        L((g)^*[ModuleCat.{u + 1} (ULift.{u + 1, u}
          (Padic.coefficientExtensionRing l E n))]) ⟶
      L((g')^*[ModuleCat.{u + 1} (ULift.{u + 1, u}
          (Padic.coefficientExtensionRing l E n))]) ⋙
        Rf_!(c.ofIsPullback
          (IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd))[
            ModuleCat.{u + 1} (ULift.{u + 1, u}
              (Padic.coefficientExtensionRing l E n))] := by
  let Λ := ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)
  letI : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n _hn
  let hsq : IsPullback g' f' f g :=
    IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd
  let c' := c.ofIsPullback hsq
  let h : c'.Z ⟶ c.Z := pullback.fst c.g g
  let eOpen : D((c.i)_!open[ModuleCat.{u + 1} Λ]) ⋙
      L((h)^*[ModuleCat.{u + 1} Λ]) ≅
      L((g')^*[ModuleCat.{u + 1} Λ]) ⋙
        D((c'.i)_!open[ModuleCat.{u + 1} Λ]) :=
    Functor.isoWhiskerLeft D((c.i)_!open[ModuleCat.{u + 1} Λ])
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) h) ≪≫
      ordinaryOpenExtensionBaseChangeIso Λ g' c'.i c.i h
        (c.isPullback_i_ofIsPullback hsq) ≪≫
      Functor.isoWhiskerRight
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) g').symm
        D((c'.i)_!open[ModuleCat.{u + 1} Λ])
  exact (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft D((c.i)_!open[ModuleCat.{u + 1} Λ])
      (derivedBaseChangeMap (ModuleCat.{u + 1} Λ)
        (c.isPullback_g_ofIsPullback hsq).flip.toCommSq) ≫
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight eOpen R((c'.g)_*[ModuleCat.{u + 1} Λ])).hom

end AlgebraicGeometry.ProEtale
