/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.PurityAffineLineDatum
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.TwistedCoordinateSectionSign
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.PurityAffineLineOrientation

import WeilConjectures.SmoothPurity.PurityFiniteSetting.Coordinate.CoordinateLocalizationCartierNormalization
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Coordinate.CoordinateLocalizationEvaluation
import WeilConjectures.AlgebraicGeometry.RelativeEffectiveCartier

/-! # Signed coordinate Cartier boundary in the published orientation chart

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
cor-pur-affine-space-zero-section-purity.proof.md, rank-one Cartier normalization
(blueprint: lem-pur-coordinate-cartier-boundary-sign).

The theorem uses the existing coordinate Cartier adjunct and the snake-normalized
support chart. The divisibility witness is quantified inside `CoordinateCartierSign`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting

private theorem coordinateZeroCartier (T : Scheme.{u}) :
    (zeroSection T).ker.IsInvertible := by
  let p : Line T ⟶ T := lineProjection T
  have : SmoothOfRelativeDimension 1 p := by
    simpa only [p, Line, lineProjection, Nat.card_ulift, Nat.card_fin] using
      AffineSpace.smoothOfRelativeDimension_over (ULift.{u} (Fin 1)) T
  let s := zeroSection T
  have hs : s ≫ p = 𝟙 T := AffineSpace.zeroSection_comp_over _ _
  let l := IsClosedImmersion.lift s s.ker.subschemeι
    (Scheme.IdealSheafData.ker_subschemeι s.ker).ge
  have : IsIso l := IsClosedImmersion.isIso_lift s s.ker.subschemeι
    (Scheme.IdealSheafData.ker_subschemeι s.ker).symm
  have hl : s.ker.subschemeι ≫ p = l := by
    rw [← IsClosedImmersion.lift_fac s s.ker.subschemeι
      (Scheme.IdealSheafData.ker_subschemeι s.ker).ge, Category.assoc, hs,
      Category.comp_id]
  have : IsIso (s.ker.subschemeι ≫ p) := hl ▸ inferInstance
  exact Scheme.IdealSheafData.isInvertible_of_isFinite_of_flat p
    inferInstance inferInstance inferInstance

/-- The coordinate zero divisor is Cartier, and its existing Cartier adjunct is the
negative of the orientation evaluating to the positive coordinate Kummer boundary.

Source: current blueprint, sec-smooth-purity/sk-prop-an,
cor-pur-affine-space-zero-section-purity.proof.md, rank-one supported Cartier calculation
(blueprint: lem-pur-coordinate-cartier-boundary-sign).

Proof: the zero section is Cartier by the relative Cartier criterion for a section
of the smooth relative curve. Take an orientation support chart from
thm-pur-affine-line-orientation and let pur be the negative of the exceptional transpose of the
explicit negative ordinary coordinate localization splice. Its support evaluation is the
positive coordinate boundary by coordinateLocalization_evaluation. The negative
ordinary splice has the relative Cartier normalization, so uniqueness identifies
the existing Cartier arrow with that inner transpose. Double negation gives
coordinateCartierAdjunct = -pur. No choice of
an arbitrary orientation or new data is involved.
-/
theorem coordinateCartierBoundarySign (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) (aT : T ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aT] [QuasiCompact aT] [IsSeparated aT] :
    P.CoordinateCartierSign T aT := by
  intro h
  obtain ⟨_, _, _, _, D, _⟩ := P.affineLine_orientation h T aT
  let hI := coordinateZeroCartier T
  refine ⟨hI, D, P.coordinateLocalizationGysin h T aT,
    P.coordinateLocalization_evaluation h T aT D, ?_⟩
  rw [← P.coordinateOrdinaryToGysin_cartier h T aT hI,
    P.coordinateCartierOrdinary_eq_of_normalization h T aT hI
      (P.coordinateLocalization_cartierNormalized h T aT hI)]
  unfold coordinateLocalizationGysin
  exact (neg_neg _).symm

end WeilConjectures.PurityFiniteSetting
