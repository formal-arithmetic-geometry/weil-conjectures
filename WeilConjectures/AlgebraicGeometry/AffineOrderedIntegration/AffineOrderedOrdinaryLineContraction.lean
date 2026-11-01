/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedEtaleSourceReassociation
public import WeilConjectures.AlgebraicGeometry.CoordinateLine.CoordinateLineAdjunctionMaps
public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedSupportedTensorCoordinates
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement

/-! # The ordinary last-line contraction before tensor coordinates -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.ProEtale.AffineOrderedIntegration
open AffineSpacePurity AffineLinePurity VectorIntegrationSite
attribute [local implicit_reducible] iteratedAffineLine iteratedAffineLineProj
  etaleCategory proCategory sourceEtale

/-- The ordinary line counit on its literal tensor source, in standing compact support.
Source: the rank-one ordinary source-coordinate formula in projection-purity agreement.
(blueprint: def-pur-affine-ordered-ordinary-line-contraction). -/
def ordinaryLineContraction
    (P : WeilConjectures.PurityFiniteSetting.{u})
    (B : Scheme.{u}) [IsNoetherian B] (aB : B ⟶ Spec (.of P.field.k))
    (J : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) B) :
    (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (AffineLinePurity.Ring P))
      (AffineSpace PUnit.{u + 1} B ↘ B)).obj
        (AffineLinePurity.etaleSource P.coefficients.l P.extension (P.level - 1)
          B P.level (annihilates P) J) ⟶ J :=
  (Etale.rightDerivedLowerShriekIso (AffineLinePurity.Ring P)
    (affineTraceLineCompactification B)).inv.app _ ≫
  (Etale.affineTraceLineLeft (AffineLinePurity.Ring P) B).map
    ((CoordinateLine.sourceCoordinates P B P.level (annihilates P) J).hom ≫
      (CoordinateLine.rightComparison (AffineLinePurity.Ring P) (exponent P)
        (annihilates P) B).inv.app J) ≫
  orderedCounitStep P B aB J 0

/-- Contract the last line before changing to ordered ordinary tensor coordinates.
Source: composition of ordinary compact support and the specified line counit.
(blueprint: def-pur-affine-ordered-ordinary-line-contraction). -/
def ordinaryEtaleCounitStep
    (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (Ke : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y) (d : ℕ) :
    (ordinaryLower P Y (d + 2)).obj (sourceEtale P Y Ke (d + 2)) ⟶
      (ordinaryLower P Y (d + 1)).obj (sourceEtale P Y Ke (d + 1)) := by
  let : IsNoetherian Y := tower_noetherian P Y aY 0
  let : IsNoetherian (iteratedAffineLine Y (d + 1)) :=
    tower_noetherian P Y aY (d + 1)
  let : IsNoetherian (iteratedAffineLine Y (d + 2)) :=
    tower_noetherian P Y aY (d + 2)
  let := (projection_geometry Y (d + 1)).2
  let := (projection_geometry Y (d + 2)).2
  exact (ordinaryLower P Y (d + 2)).map (etaleSourceReassociation P Y aY Ke d).hom ≫
    (Etale.unboundedEtaleLowerShriekCompIso (AffineLinePurity.Ring P)
      (lastProjection Y (d + 1)) (iteratedAffineLineProj Y (d + 1))).inv.app _ ≫
    (ordinaryLower P Y (d + 1)).map
      (ordinaryLineContraction P (iteratedAffineLine Y (d + 1))
        (towerBase aY (d + 1)) (sourceEtale P Y Ke (d + 1)))

/-- The site and standing-compactification coordinates, before the tensor coordinates.
Source: the definition of supportedTensorCoordinates.
(blueprint: def-pur-affine-ordered-ordinary-line-contraction). -/
def ordinarySupportCoordinates
    (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) [IsNoetherian Y]
    (Ke : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y) (d : ℕ)
    (hJ : DerivedCategory.TStructure.t.plus (sourceEtale P Y Ke d)) :
    letI := (projection_geometry Y d).2
    (rightDerivedLowerShriek (ModuleCat.{u + 1} (AffineLinePurity.Ring P))
      (iteratedAffineLineProj Y d)).obj
        ((comparison (AffineLinePurity.Ring P) (iteratedAffineLine Y d)).obj
          (sourceEtale P Y Ke d)) ≅
      (comparison (AffineLinePurity.Ring P) Y).obj
        ((ordinaryLower P Y d).obj (sourceEtale P Y Ke d)) := by
  letI := (projection_geometry Y d).2
  exact (compactSupportSiteComparison (AffineLinePurity.Ring P)
      (compactification Y d)).app ⟨_, hJ⟩ ≪≫
    (comparison (AffineLinePurity.Ring P) Y).mapIso
      ((Etale.rightDerivedLowerShriekIso (AffineLinePurity.Ring P)
        (compactification Y d)).app (sourceEtale P Y Ke d))

end AlgebraicGeometry.ProEtale.AffineOrderedIntegration
