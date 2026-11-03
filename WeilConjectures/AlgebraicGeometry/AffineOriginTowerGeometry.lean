/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceCompactComparisonRestriction
public import WeilConjectures.AlgebraicGeometry.Affine.Space.AffineSpaceTopTrace
public import WeilConjectures.AlgebraicGeometry.AffineSpaceCharts
public import WeilConjectures.AlgebraicGeometry.CoordinateCounitArrows.CoordinateCounitArrows
public import WeilConjectures.AlgebraicGeometry.Ordered.OrderedAffineTraceNormalForm
public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceLinePurity
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedCartierKummerSupplement
public import WeilConjectures.EtaleCohomology.Purity.Smooth.SupportedCup
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportComparisons
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.AffineSpace.ZeroSection
import all WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceTower

/-! # The actual origin in the ordered affine tower

Source: `det-sp-trace-basic`, Proof (2), coordinate sections and their composition
(blueprint: lem-sp-affine-origin-tower-geometry).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- The tower origin is a section of the projection.
Source: coordinate geometry in `det-sp-trace-basic`, Proof (2)
(blueprint: lem-sp-affine-origin-tower-geometry).
Proof: cancel the fixed affine-space isomorphism and apply the zero-section equation. -/
@[reassoc]
theorem affineOriginTowerZeroSection_over (S : Scheme.{u}) (d : ℕ) :
    affineOriginTowerZeroSection S d ≫ affineTraceProjection S d = 𝟙 S := by
  have hp : (affineTraceAffineSpaceIso S d).inv ≫ affineTraceProjection S d =
      AffineSpace (ULift.{u} (Fin d)) S ↘ S := by
    apply (cancel_epi (affineTraceAffineSpaceIso S d).hom).mp
    simp only [Iso.hom_inv_id_assoc]
    exact (AffineSpace.homOfVector_over _ _).symm
  dsimp only [affineOriginTowerZeroSection]
  rw [Category.assoc, hp, AffineSpace.zeroSection_comp_over]

/-- Every ordered coordinate vanishes at the tower origin.
Source: coordinate geometry in `det-sp-trace-basic`, Proof (2)
(blueprint: lem-sp-affine-origin-tower-geometry).
Proof: the fixed affine-space isomorphism identifies the coordinates; its composite
with the transported zero section is the ordinary zero section. -/
theorem affineOriginTowerZeroSection_coord (S : Scheme.{u}) (d : ℕ) (i : Fin d) :
    (affineOriginTowerZeroSection S d).appTop (affineTraceCoordinate S d i) = 0 := by
  have hc : (affineTraceAffineSpaceIso S d).hom.appTop
      (AffineSpace.coord S (ULift.up i)) = affineTraceCoordinate S d i := by
    simp [affineTraceAffineSpaceIso, affineTraceToAffineSpace]
  rw [← hc, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]
  simp [affineOriginTowerZeroSection]

/-- In rank zero the transported origin is the identity morphism.
Source: empty coordinate list in `det-sp-trace-basic`, Proof (2)
(blueprint: lem-sp-affine-origin-tower-geometry).
Proof: its composite with the rank-zero projection, which is identity, is identity. -/
theorem affineOriginTowerZeroSection_zero (S : Scheme.{u}) :
    affineOriginTowerZeroSection S 0 = 𝟙 S := by
  have h := affineOriginTowerZeroSection_over S 0
  change affineOriginTowerZeroSection S 0 ≫ 𝟙 S = 𝟙 S at h
  exact (Category.comp_id _).symm.trans h

/-- The successor origin is the previous origin followed by the last zero section.
Source: coordinate geometry in `det-sp-trace-basic`, Proof (2)
(blueprint: lem-sp-affine-origin-tower-geometry).
Proof: both morphisms have projection identity and all polynomial coordinates zero.
The affine tower hom extensionality lemma identifies them, including rank zero. -/
theorem affineOriginTowerZeroSection_succ (S : Scheme.{u}) (d : ℕ) :
    affineOriginTowerZeroSection S d ≫
      AffineSpace.zeroSection PUnit.{u + 1} (affineTraceTower S d) =
        affineOriginTowerZeroSection S (d + 1) := by
  apply affineTraceTower_hom_ext (d + 1)
  · rw [affineOriginTowerZeroSection_over]
    change (affineOriginTowerZeroSection S d ≫
      AffineSpace.zeroSection PUnit.{u + 1} (affineTraceTower S d)) ≫
        ((AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d) ≫
          affineTraceProjection S d) = 𝟙 S
    rw [Category.assoc, ← Category.assoc
      (AffineSpace.zeroSection PUnit.{u + 1} (affineTraceTower S d)),
      AffineSpace.zeroSection_comp_over, Category.id_comp]
    exact affineOriginTowerZeroSection_over S d
  · intro i
    rw [affineOriginTowerZeroSection_coord]
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · have hz := congrArg (fun r ↦ (affineOriginTowerZeroSection S d).appTop r)
        (AffineSpace.zeroSection_appTop_coord PUnit.{u + 1}
          (affineTraceTower S d) PUnit.unit)
      simpa only [affineTraceCoordinate, Fin.lastCases_last, Scheme.Hom.comp_appTop,
        CommRingCat.comp_apply, map_zero] using! hz
    · have hp : (affineOriginTowerZeroSection S d ≫
          AffineSpace.zeroSection PUnit.{u + 1} (affineTraceTower S d)) ≫
          (AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d) =
            affineOriginTowerZeroSection S d := by
        rw [Category.assoc, AffineSpace.zeroSection_comp_over, Category.comp_id]
      have hz : ((affineOriginTowerZeroSection S d ≫
          AffineSpace.zeroSection PUnit.{u + 1} (affineTraceTower S d)) ≫
          (AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d)).appTop
            (affineTraceCoordinate S d j) = 0 := by
        rw [hp]
        exact affineOriginTowerZeroSection_coord S d j
      simpa only [affineTraceCoordinate, Fin.lastCases_castSucc,
        Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using! hz

/-- Canonical direct-image composition at the successor origin.
Source: closed-support composition in `det-sp-trace-basic`, Proof (2)
(blueprint: lem-sp-affine-origin-tower-geometry). -/
def affineOriginClosedSourceIso
    (A : Type (u + 1)) [CommRing A] (S : Scheme.{u}) (d : ℕ) :
    (ordinaryFinitePushforward A (affineOriginTowerZeroSection S (d + 1))).obj
        (ordinaryFiniteUnit A S) ≅
      (ordinaryFinitePushforward A
        (AffineSpace.zeroSection PUnit.{u + 1} (affineTraceTower S d))).obj
        ((ordinaryFinitePushforward A (affineOriginTowerZeroSection S d)).obj
          (ordinaryFiniteUnit A S)) :=
  ((rightDerivedLowerStarCompIsoOfComp (ModuleCat.{u + 1} A)
    (affineOriginTowerZeroSection S d)
    (AffineSpace.zeroSection PUnit.{u + 1} (affineTraceTower S d))
    (affineOriginTowerZeroSection S (d + 1)) (affineOriginTowerZeroSection_succ S d)).app _).symm

end AlgebraicGeometry.Etale
