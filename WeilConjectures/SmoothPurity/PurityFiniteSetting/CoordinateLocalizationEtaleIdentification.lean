/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Coordinate.CoordinateBoundaryGeometricPullback
public import WeilConjectures.AlgebraicGeometry.Supported.SupportedHomCocycleNormalization

/-! # Normalized étale supported-Hom identification for the coordinate pair

Source: Milne, Lectures on Etale Cohomology, Section 9, Example 9.5 and the
proof of Theorem 9.4 (blueprint: lem-pur-coordinate-localization-splice-support-class-etale).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting

/-- The prescribed étale supported-Hom identification is represented by a
cocycle-normalized comparison record, and the comparison agrees with every
identification carried by a coordinate boundary model.

Source: Milne, Section 9, Example 9.5 and the injective-resolution proof of
Theorem 9.4; the support-kernel evaluation at one determines the comparison.
Proof: choose the normalized evaluation/cocycle record for the zero-section
support pair.  On an injective representative, the evaluation map identifies
every supported cycle with a unique map from the supported constant sheaf.
The normalization field of the given identification and the cocycle field of
the chosen record therefore agree on every cycle; injective resolutions and
naturality extend this equality to all bounded-below objects.
(blueprint: new-lem-pur-coordinate-localization-etale-identification).
-/
theorem coordinateLocalization_etale_identification_normalization
    (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (M : CoordinateBoundaryModel P T) :
    ∃ N : SupportedHomCocycleNormalization
        (etaleSupportHomPair P (zeroSection T)).topology P.Coefficient
        (etaleSupportHomPair P (zeroSection T)).isTerminal
        (etaleSupportHomPair P (zeroSection T)).restriction
        (etaleSupportHomPair P (zeroSection T)).supported
        (etaleSupportHomPair P (zeroSection T)).constantRestriction,
      ∀ (K : DerivedCategory.Plus
          (Sheaf (Line T).smallEtaleTopology
            (ModuleCat.{u + 1} P.Coefficient))) (a : ℤ),
        M.chiEtale.chi K a = N.chi K a := by
  sorry

end WeilConjectures.PurityFiniteSetting
