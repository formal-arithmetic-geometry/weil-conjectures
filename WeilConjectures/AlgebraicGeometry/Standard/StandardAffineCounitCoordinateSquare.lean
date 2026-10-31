/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoordinateCounitArrows.CoordinateCounitArrows

/-! Coordinate square underlying the standard affine transport.
(blueprint: lem-trf-standard-affine-counit-coordinate-square).

Proof: compare the structure map and each recursive polynomial coordinate; the
zero-variable case is the identity. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Etale

private theorem coordinate_square_coord {T S : Scheme.{u}} (v : T ⟶ S) (d : ℕ)
    (j : Fin d) :
    (affineTraceMap v d).appTop (affineTraceCoordinate S d j) =
      affineTraceCoordinate T d j := by
  induction d with
  | zero => exact Fin.elim0 j
  | succ d ih =>
    refine Fin.lastCases ?_ (fun i ↦ ?_) j
    · simpa only [affineTraceCoordinate, Fin.lastCases_last, affineTraceMap] using!
        (AffineSpace.map_appTop_coord (affineTraceMap v d) PUnit.unit)
    · simp only [affineTraceCoordinate, Fin.lastCases_castSucc]
      change (affineTraceMap v (d + 1)).appTop
        ((AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘
          affineTraceTower S d).appTop (affineTraceCoordinate S d i)) = _
      erw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]
      change ((AffineSpace.map PUnit.{u + 1} (affineTraceMap v d)) ≫
        AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d).appTop _ = _
      rw [AffineSpace.map_over, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, ih]

/-- The affine trace coordinate isomorphisms form the Cartesian square used by
the standard affine counit transport.
Source: sk-thm-dnc, local construction, standard affine model
(blueprint: lem-trf-standard-affine-counit-coordinate-square).
Proof: both sides lie over `S` by the tower pullback square, and the `i`th affine
coordinate pulls back along both sides to the `i`th tower coordinate of `T`
(`coordinate_square_coord`); conclude by `AffineSpace.hom_ext`.
-/
theorem standardAffineCounit_coordinateSquare
    {S T : Scheme.{u}} (v : T ⟶ S) (d : ℕ) :
    affineTraceMap v d ≫ (affineTraceAffineSpaceIso S d).hom =
      (affineTraceAffineSpaceIso T d).hom ≫
        AffineSpace.map (ULift.{u} (Fin d)) v := by
  apply AffineSpace.hom_ext
  · simp only [Category.assoc, affineTraceAffineSpaceIso, asIso_hom,
      affineTraceToAffineSpace, AffineSpace.homOfVector_over, AffineSpace.homOfVector_over_assoc,
      AffineSpace.map_over]
    exact (affineTraceMap_isPullback v d).w
  · rintro ⟨i⟩
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, affineTraceAffineSpaceIso,
      asIso_hom, affineTraceToAffineSpace, AffineSpace.homOfVector_appTop_coord,
      AffineSpace.map_appTop_coord]
    exact coordinate_square_coord v d i


end AlgebraicGeometry.Etale
