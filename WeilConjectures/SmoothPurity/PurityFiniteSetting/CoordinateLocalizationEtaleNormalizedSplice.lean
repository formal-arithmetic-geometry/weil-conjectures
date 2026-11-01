/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Coordinate.CoordinateBoundaryGeometricPullback
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Coordinate.CoordinateLocalizationSplice
public import WeilConjectures.AlgebraicGeometry.Supported.SupportedHomCocycleNormalization

/-! # Normalized coordinate localization splice on the étale site

Source: Milne, Lectures on Etale Cohomology, Section 9, Theorem 9.4 and
Example 9.5 (blueprint: lem-pur-coordinate-localization-splice-support-class-etale).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting

/-- A cocycle-normalized supported-Hom comparison evaluates the negative
coordinate boundary on the negative Yoneda localization splice.

Source: Milne, Section 9, Theorem 9.4 and Example 9.5, pp. 65--67; the
open-closed localization sequence and the degree-one Kummer cocycle.
Proof: resolve the twisted coefficient object by a bounded-below injective
complex.  Lift the degree-one coordinate Kummer cocycle through the epimorphic
restriction map.  Its differential is the snake boundary in the support
kernel complex.  Ext-class naturality identifies the resulting localized
cocycle with the Yoneda product defining `coordinateLocalizationClass`; the
cocycle normalization evaluates the supported map on the constant unit.  The
inverse closed constant comparison and the additive sign give the displayed
negative equality.
(blueprint: new-lem-pur-coordinate-localization-etale-normalized-splice).
-/
theorem coordinateLocalization_etale_normalized_splice
    (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (T : Scheme.{u})
    (aT : T ⟶ Spec (.of P.field.k)) (M : CoordinateBoundaryModel P T)
    (N : SupportedHomCocycleNormalization
      (etaleSupportHomPair P (zeroSection T)).topology P.Coefficient
      (etaleSupportHomPair P (zeroSection T)).isTerminal
      (etaleSupportHomPair P (zeroSection T)).restriction
      (etaleSupportHomPair P (zeroSection T)).supported
      (etaleSupportHomPair P (zeroSection T)).constantRestriction) :
    N.chi (P.coordinateEtaleInput h (Line T)) 2
        (-M.alphaEtale P h aT) =
      (-P.coordinateLocalizationClass h T aT).hom := by
  sorry

end WeilConjectures.PurityFiniteSetting
