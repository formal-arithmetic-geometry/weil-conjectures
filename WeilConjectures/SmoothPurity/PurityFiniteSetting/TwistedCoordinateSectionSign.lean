/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoordinateSectionNormalization.TwistedCoordinateSectionMaps
public import WeilConjectures.SixFunctors.Etale.Derived.AdjunctionShift

/-! # The coordinate Cartier sign in the published orientation chart
Source: current blueprint, sec-smooth-purity/sk-prop-an,
cor-pur-affine-space-zero-section-purity.proof.md; signed relative-cone normalization
(blueprint: def-pur-coordinate-section-cartier-sign).

This is the same supported Cartier arrow, written directly in the coordinate and
coefficient presentation of the already recorded affine-line orientation. Thus no
arbitrary coordinate or coefficient isomorphism is needed to compare the two signs.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.RetractedSupport

/-- The actual ordinary positive Cartier arrow in the affine-line datum's coordinates.
The unique relative-boundary normalization fixes its supported sign.
Source: blueprint Step 7, principal-frame e=t^-1 and tau=t*e
(blueprint: def-pur-coordinate-section-cartier-sign). -/
def coordinateCartierOrdinary (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (T : Scheme.{u})
    (aT : T ⟶ Spec (.of P.field.k))
    (hI : (zeroSection T).ker.IsInvertible) :=
  Etale.supportedExactDerivedMap
    (Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) (zeroSection T))
    (P.constantEtale T) (P.twistEtale h (Line T))
    ((Etale.ordinary_supported_kummer_uniqueBoundary (Line T) P.exponent
      (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) P.Coefficient
      (P.exponent_coefficient_eq_zero h)
      (by simpa only [exponent, Nat.cast_pow] using
        (ProEtale.AffineLinePurity.primeUnit P (Line T)
          (lineProjection T ≫ aT)).pow P.kummerLevel)
      (zeroSection T) hI).exists.choose)

/-- The ordinary closed exceptional adjunct, using the canonical proper/closed
comparison and its actual adjunction. Source: blueprint Step 7
(blueprint: def-pur-coordinate-section-cartier-sign). -/
def coordinateCartierOrdinaryAdjunct (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (T : Scheme.{u})
    (aT : T ⟶ Spec (.of P.field.k))
    (hI : (zeroSection T).ker.IsInvertible) :=
  ((Etale.rightDerivedUpperShriekAdjunction P.Coefficient
    (zeroSection T)).ofNatIsoLeft
      (Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar
        (ModuleCat.{u + 1} P.Coefficient) (zeroSection T))).homEquiv _ _
          (P.coordinateCartierOrdinary h T aT hI)

/-- The positive Cartier adjunct on the pro-etale site in the literal Gysin chart.
The factors are the single/comparison inverse, the transported ordinary adjunct,
the two canonical shift comparisons, and the shifted comparison-unit map rho.
Source: blueprint u_s and finite-site transport, Steps 5 and 7
(blueprint: def-pur-coordinate-section-cartier-sign). -/
def coordinateCartierAdjunct (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (T : Scheme.{u})
    (aT : T ⟶ Spec (.of P.field.k))
    (hI : (zeroSection T).ker.IsInvertible) :
    P.derivedSheaf h T false ⟶ P.gysinValue h T :=
  ((comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategorySingleFunctor
    0).inv.app (P.constantEtale T) ≫
    (nu P T).map (P.coordinateCartierOrdinaryAdjunct h T aT hI) ≫
    (nu P T).map
      (((Etale.rightDerivedUpperShriek P.Coefficient
        (zeroSection T)).commShiftIso (2 : ℤ)).hom.app
          (P.gysinEtaleInput h T).obj) ≫
    ((nu P T).commShiftIso (2 : ℤ)).hom.app _ ≫
    (shiftFunctor _ (2 : ℤ)).map
      (boundedSiteRho P.Coefficient
        (Etale.rightDerivedUpperShriek P.Coefficient (zeroSection T))
        (P.gysinEtaleInput h T).obj)

/-- The supported Cartier adjunct is the negative of the positive localization-boundary
orientation. Both maps use the published Gysin identification and the signed cone
D(a,b)=(da,r(a)-db), whose connecting representative is (0,-b).
Source: blueprint Step 7, as corrected in the DAG sign audit
(blueprint: def-pur-coordinate-section-cartier-sign). -/
def CoordinateCartierSign (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (aT : T ⟶ Spec (.of P.field.k)) : Prop :=
  ∀ h : P.ramificationIndex ∣ P.level,
    ∃ hI : (zeroSection T).ker.IsInvertible,
    ∃ D : OrientationSupportData P h T,
    ∃ pur : P.derivedSheaf h T false ⟶ P.gysinValue h T,
      D.support.hom (P.gysinHomToSections h T pur) = D.coordinateBoundary P h aT ∧
      P.coordinateCartierAdjunct h T aT hI = -pur

end WeilConjectures.PurityFiniteSetting
