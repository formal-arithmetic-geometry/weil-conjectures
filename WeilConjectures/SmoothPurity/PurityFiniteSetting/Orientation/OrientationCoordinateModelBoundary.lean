/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.PurityAffineLineOrientationData

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Coordinate.CoordinateBoundaryGeometricPullback
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.PurityAffineLineOrientationData

/-! # Agreement of the two coordinate-boundary presentations

Source: blueprint affine-line orientation, geometric-fibre sentence; Milne, Section 9
(blueprint: lem-pur-orientation-coordinate-model-boundary).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.RetractedSupport

namespace WeilConjectures.PurityFiniteSetting

/-- The Gysin chart and the ordinary/pro-etale coordinate model represent the same
supported class. Only the coordinate boundary is compared; no pullback or residue
normalization is asserted.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-lem-sp-reduction/thm-pur-affine-line-orientation.proof.md, coordinate-boundary sentence;
Milne, Theorem 9.4 and Example 9.5
(blueprint: lem-pur-orientation-coordinate-model-boundary).

Proof: Identify coordinateProInput with gysinInput. In degree one the right-derived
comparison sends evaluation of the Ext morphism on the constant unit to its global
cohomology class. Both coordinateEtaleOpenClass and gysinKummerSection use exactly
this evaluation, the inverse canonical root-line pullback, and the canonical open
localization isomorphism. The comparison unit and comparisonUpperStarCompUpperStarIso
therefore identify their open sections; uniqueness of isomorphisms over Line Y
identifies the two presentations of the open complement. On a bounded-below injective
resolution, D.boundary_normalized and M.pro_normalized identify their model boundaries
with ShortExact.delta for the identical supported-kernel and restriction sequence.
Proof irrelevance identifies its short-exactness witnesses. Cancel the canonical
supportSequenceModelIso isomorphisms to identify the boundary components on that
representative. Naturality and an injective resolution of the input extend the equality
to gysinInput. Applying this boundary equality to the already identified open sections
gives the displayed equality with its specified sign. This works for arbitrary Y
and a, including the empty scheme; finite type is unnecessary for this comparison. -/
theorem orientation_coordinate_model_boundary (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k))
    (D : OrientationSupportData P h Y) (M : CoordinateBoundaryModel P Y) :
    D.coordinateBoundary P h a = M.alphaPro P h a := by
  change (D.boundary 1).app ⟨P.gysinInput h Y, trivial⟩
      (P.gysinKummerSection h Y a D.comparison D.openCoefficient) =
    M.alphaPro P h a
  rw [P.orientation_coordinate_boundary_normalization h Y D M,
    P.orientation_coordinate_open_class h Y a D M]
  rfl

end WeilConjectures.PurityFiniteSetting
