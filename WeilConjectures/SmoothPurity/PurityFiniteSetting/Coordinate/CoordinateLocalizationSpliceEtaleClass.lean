/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Coordinate.CoordinateLocalizationSplice
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Coordinate.CoordinateBoundaryGeometricPullback
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.CoordinateLocalizationEtaleIdentification
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.CoordinateLocalizationEtaleNormalizedSplice

/-! # Etale supported-Hom realization of the coordinate localization splice

Source: Milne, Lectures on Etale Cohomology, Section 9, Theorem 9.4 and
Proposition 9.6; current blueprint, cor-pur-affine-space-zero-section-purity.proof.md,
rank-one coordinate localization paragraph
(blueprint: lem-pur-coordinate-localization-splice-support-class-etale).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting

/-- The ordinary coordinate localization splice is the snake-normalized class on
 the etale support model.  This is the injective-resolution calculation before
 applying the etale-to-proetale comparison.

Proof plan: resolve the twist by a bounded-below injective complex.  Lift the
coordinate Kummer cocycle through the surjective restriction map furnished by
the open-closed short exact sequence.  The differential of the lift is the
snake boundary in the support kernel cone.  Ext-class naturality identifies the
Yoneda product defining `coordinateLocalizationClass` with this differential,
and the cocycle normalization of `M.chiEtale` identifies its evaluation on one.
Negation is carried through the additive comparison maps.

Source: Milne, Section 9, Theorem 9.4 and Example 9.5
(blueprint: lem-pur-coordinate-localization-splice-support-class-etale).
-/
theorem coordinateLocalization_spliceSupportClass_etale (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (T : Scheme.{u})
    (aT : T ⟶ Spec (.of P.field.k))
    (M : CoordinateBoundaryModel P T) :
    M.chiEtale.chi (P.coordinateEtaleInput h (Line T)) 2
        (-M.alphaEtale P h aT) =
      (-P.coordinateLocalizationClass h T aT).hom := by
  obtain ⟨N, hN⟩ := coordinateLocalization_etale_identification_normalization P T M
  rw [hN (P.coordinateEtaleInput h (Line T)) 2]
  exact coordinateLocalization_etale_normalized_splice P h T aT M N

end WeilConjectures.PurityFiniteSetting
