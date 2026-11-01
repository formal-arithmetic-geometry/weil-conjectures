/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Coordinate.CoordinateLocalizationSplice
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.PurityAffineLineOrientationData
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

import WeilConjectures.SmoothPurity.PurityFiniteSetting.Coordinate.CoordinateLocalizationSpliceSupportClass
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Coordinate.CoordinateOrdinaryGysinSupportEvaluation
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Coordinate.CoordinateLocalizationSupportNegation
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Orientation.OrientationCoordinateModelBoundary

/-! # Evaluation of the coordinate localization splice in the orientation chart

Source: current blueprint, cor-pur-affine-space-zero-section-purity.proof.md,
rank-one paragraph and finite etale-origin transport paragraph
(blueprint: lem-pur-coordinate-localization-evaluation).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits

namespace WeilConjectures.PurityFiniteSetting

/-- The ordinary positive localization splice evaluates to the snake-normalized
positive supported coordinate boundary in every published orientation chart.
This comparison makes no reference to a Cartier ideal or to its torsor class.
Source: current blueprint, cor-pur-affine-space-zero-section-purity.proof.md,
rank-one and finite etale-origin transport paragraphs
(blueprint: lem-pur-coordinate-localization-evaluation).

Proof: choose a coordinate boundary model M by coordinate_boundary_geometric_pullback,
and obtain a canonical site transport v from supportedHom_pullback applied to the
identity Cartesian square of the zero section; no geometric point is needed, so the
empty base is included. By coordinateLocalization_spliceSupportClass, M.chiPro sends
-M.alphaPro to the site image of the negative localization Ext class. Apply
coordinateOrdinary_gysinSupportEvaluation to that negative class and rewrite its right
side by this equality; the inverse additive equivalence cancels M.chiPro, so supported
evaluation of coordinateOrdinaryToGysin of the ordinary negative splice is -M.alphaPro.
By definition coordinateLocalizationGysin is minus that Gysin morphism;
gysinSupportEvaluation_neg moves the minus through supported evaluation, and neg_neg
gives M.alphaPro. Finally orientation_coordinate_model_boundary identifies M.alphaPro
with D.coordinateBoundary. All maps are additive, so empty schemes and
characteristic two need no exception. -/
theorem coordinateLocalization_evaluation (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (T : Scheme.{u})
    (aT : T ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aT] [QuasiCompact aT] [IsSeparated aT]
    (D : OrientationSupportData P h T) :
    D.support.hom (P.gysinHomToSections h T (P.coordinateLocalizationGysin h T aT)) =
      D.coordinateBoundary P h aT := by
  obtain ⟨M, _⟩ := P.coordinate_boundary_geometric_pullback h T aT
  obtain ⟨chiE, chiP, ht⟩ := supportedHom_pullback P
  let hi := IsPullback.id_horiz (zeroSection T)
  let sq : ChosenCartesianSquare (𝟙 T) (zeroSection T) (zeroSection T) (𝟙 (Line T)) :=
    { toCommSq := hi.toCommSq
      isoPullback := hi.isoPullback
      hom_fst := hi.isoPullback_hom_fst
      hom_snd := hi.isoPullback_hom_snd }
  obtain ⟨e, p, v, v', hv⟩ := ht (zeroSection T) (zeroSection T)
    (𝟙 (Line T)) (𝟙 T) sq
  have hclass := P.coordinateLocalization_spliceSupportClass h T aT M v
  have heval := P.coordinateOrdinary_gysinSupportEvaluation h T aT D M.chiPro v
    (-P.coordinateLocalizationClass h T aT)
  rw [← hclass] at heval
  simp only [AddEquiv.symm_apply_apply] at heval
  change D.support.hom (P.gysinHomToSections h T
    (-P.coordinateOrdinaryToGysin h T (P.coordinateLocalizationOrdinaryNegative h T aT))) = _
  rw [gysinSupportEvaluation_neg]
  change -(D.support.hom (P.gysinHomToSections h T
    (P.coordinateOrdinaryToGysin h T (Etale.supportedExactDerivedMap _ _ _
      (-P.coordinateLocalizationClass h T aT))))) = _
  rw [heval, neg_neg]
  exact (P.orientation_coordinate_model_boundary h T aT D M).symm

end WeilConjectures.PurityFiniteSetting
