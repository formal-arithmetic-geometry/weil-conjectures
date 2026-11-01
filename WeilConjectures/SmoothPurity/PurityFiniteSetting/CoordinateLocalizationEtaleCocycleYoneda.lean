/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Coordinate.CoordinateLocalizationSplice
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Coordinate.CoordinateBoundaryGeometricPullback
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.CoordinateLocalizationEtaleBoundaryCocycle

/-! # Yoneda identification of the coordinate boundary cocycle

Source: Milne, Lectures on Etale Cohomology, Section 9, Theorem 9.4 and
Example 9.5 (blueprint: lem-pur-coordinate-localization-etale-cocycle-yoneda).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting

/-- The cocycle witness is the negative Yoneda localization splice.

Source: Milne, Section 9, Theorem 9.4 and Example 9.5, pp. 65--67.
Proof: lift the degree-one coordinate Kummer cocycle through the open restriction.
The differential of the lift is the snake boundary; `ShortExact.extClass_naturality`
and `extClass_hom` identify its localized cocycle with `coordinateLocalizationClass`.
The inverse closed constant comparison and the additive sign give the result.
(blueprint: lem-pur-coordinate-localization-etale-cocycle-yoneda).
-/
theorem coordinateLocalization_etale_cocycle_yoneda
    (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (T : Scheme.{u})
    (aT : T ⟶ Spec (.of P.field.k)) (M : CoordinateBoundaryModel P T)
    (N : SupportedHomCocycleNormalization
      (etaleSupportHomPair P (zeroSection T)).topology P.Coefficient
      (etaleSupportHomPair P (zeroSection T)).isTerminal
      (etaleSupportHomPair P (zeroSection T)).restriction
      (etaleSupportHomPair P (zeroSection T)).supported
      (etaleSupportHomPair P (zeroSection T)).constantRestriction)
    (W : CoordinateLocalizationEtaleWitness P h T aT M) :
    N.chi (P.coordinateEtaleInput h (Line T)) 2
        (-M.alphaEtale P h aT) =
      (-P.coordinateLocalizationClass h T aT).hom := by
  sorry

end WeilConjectures.PurityFiniteSetting
