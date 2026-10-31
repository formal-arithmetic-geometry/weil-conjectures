/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Coordinate.CoordinateLocalizationSplice
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.PurityAffineLineOrientationData
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Coordinate.CoordinateLocalizationSpliceEtaleClass
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Coordinate.CoordinateLocalizationSpliceSiteComparison

/-! # Supported-Hom realization of the coordinate Yoneda splice

Source: Milne, Section 9, Theorem 9.4, Example 9.5 and Proposition 9.6; current blueprint,
cor-pur-affine-space-zero-section-purity.proof.md, rank-one localization calculation
(blueprint: lem-pur-coordinate-localization-splice-support-class).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting

private theorem splice_eq {α β : Sort*} (f : α → β) {a b : α} {c : β}
    (hs : c = f a) (he : a = b) : c = f b :=
  hs.trans (congrArg f he)

/-- The negative ordinary Yoneda splice represents the negative normalized coordinate
boundary under supported Hom and the canonical site comparison. This calculation uses
no exceptional inverse image or orientation support chart.

Source: Milne, Section 9, Theorem 9.4, Example 9.5 and Proposition 9.6; current blueprint,
cor-pur-affine-space-zero-section-purity.proof.md, rank-one paragraph
(blueprint: lem-pur-coordinate-localization-splice-support-class).

Proof: resolve the twist by a bounded-below injective complex. The open-closed
coefficient sequence makes restriction of Hom into each injective surjective.
Lift the degree-one open Kummer cocycle z to r. The localization Yoneda product
is represented by dr: the differential on the shifted resolution cancels the
negative resolution representative of the extension. In the relative cone,
D(r,0)+(0,-z)=(dr,0) identifies that representative with the positive snake boundary.
The inverse closed constant comparison and the open constant, root-pullback and
counit factors in coordinateLocalizationClass fix evaluation on one. Apply
SupportedHomCocycleNormalization and the two normalization fields of M to obtain
the same supported-Hom class. Exact site comparison preserves the coefficient
unit, the root pullback and the snake boundary, while v.closedIso_spec fixes the
supported constant comparison. Naturality transports the equation off the
injective model. Finally negate the equation. All operations are additive, so
empty schemes and characteristic two require no exception.
-/
theorem coordinateLocalization_spliceSupportClass (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (T : Scheme.{u})
    (aT : T ⟶ Spec (.of P.field.k))
    (M : CoordinateBoundaryModel P T) (v : siteSupportHomTransport P (zeroSection T)) :
    M.chiPro.chi (P.coordinateProInput h (Line T)) 2 (-M.alphaPro P h aT) =
      v.homMap (hB := Scheme.isContinuous_toProEt (Line T))
        (P.coordinateEtaleInput h (Line T)) 2
        (-P.coordinateLocalizationClass h T aT).hom := by
  exact splice_eq
    (v.homMap (hB := Scheme.isContinuous_toProEt (Line T))
      (P.coordinateEtaleInput h (Line T)) 2)
    (coordinateLocalization_spliceSupportClass_site P h T aT M v)
    (coordinateLocalization_spliceSupportClass_etale P h T aT M)

end WeilConjectures.PurityFiniteSetting
