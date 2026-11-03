/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.DiagonalPasting.PurityDiagonalSectionPastingData
public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceTower

/-! # The actual affine coordinate charts for the two ordered blocks -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting.AffineOrdinaryIntegrationCoordinates

/-- Split the finite coordinates using the actual Cartesian square of block projections.
Source: composition proof Step 1, the standard coordinates in which the tangent sequence splits.
(blueprint: new-pur-affine-integration-ordinary-coordinate-geometry).
The unique isomorphism of the two pullback cones preserves both projections, also at rank zero. -/
def split (B : Scheme.{u}) (d e : ℕ) :
    DiagonalPasting.A (d + e) B ≅ DiagonalPasting.A d (DiagonalPasting.A e B) :=
  IsPullback.isoIsPullback (DiagonalPasting.A d B) (DiagonalPasting.A e B)
    (DiagonalPasting.affineGeometry d e B).1
    (AffineSpace.isPullback_map (n := ULift.{u} (Fin d)) (DiagonalPasting.pr e B))

/-- The split chart preserves the projection to the second coordinate block. -/
theorem split_over (B : Scheme.{u}) (d e : ℕ) :
    (split B d e).hom ≫ DiagonalPasting.pr d (DiagonalPasting.A e B) =
      DiagonalPasting.q d e B :=
  IsPullback.isoIsPullback_hom_snd (DiagonalPasting.A d B) (DiagonalPasting.A e B)
    (DiagonalPasting.affineGeometry d e B).1 _

/-- The same chart preserves the first block, fixing the order of the coordinates. -/
theorem split_first (B : Scheme.{u}) (d e : ℕ) :
    (split B d e).hom ≫
        AffineSpace.map (ULift.{u} (Fin d)) (DiagonalPasting.pr e B) =
      DiagonalPasting.first d e B :=
  IsPullback.isoIsPullback_hom_fst (DiagonalPasting.A d B) (DiagonalPasting.A e B)
    (DiagonalPasting.affineGeometry d e B).1 _

/-- The finite-coordinate chart of the literal affine-line tower preserves its projection. -/
theorem tower_chart_over (B : Scheme.{u}) (d : ℕ) :
    (affineTraceAffineSpaceIso B d).inv ≫ affineTraceProjection B d =
      DiagonalPasting.pr d B := by
  apply (cancel_epi (affineTraceAffineSpaceIso B d).hom).mp
  simp only [Iso.hom_inv_id_assoc]
  exact (AffineSpace.homOfVector_over _ _).symm

/-- The chart for q, obtained by splitting blocks and then taking the ordered affine-line chart. -/
def blockChart (B : Scheme.{u}) (d e : ℕ) :
    DiagonalPasting.A (d + e) B ≅ affineTraceTower (DiagonalPasting.A e B) d :=
  split B d e ≪≫ (affineTraceAffineSpaceIso (DiagonalPasting.A e B) d).symm

/-- The actual block chart is a chart over the prescribed map q. -/
theorem blockChart_over (B : Scheme.{u}) (d e : ℕ) :
    (blockChart B d e).hom ≫ affineTraceProjection (DiagonalPasting.A e B) d =
      DiagonalPasting.q d e B := by
  simp only [blockChart, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    tower_chart_over, split_over]

end WeilConjectures.PurityFiniteSetting.AffineOrdinaryIntegrationCoordinates
