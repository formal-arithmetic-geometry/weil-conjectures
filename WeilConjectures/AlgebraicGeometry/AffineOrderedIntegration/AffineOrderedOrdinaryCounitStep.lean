/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedOrdinaryLineContraction
import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceCompactComparisonRestriction

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

-- The bounded-below ordinary comparison is the restriction of the unbounded tower map.
private theorem compactComparison_unbounded_for_recursion
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (Y : Scheme.{u}) [IsNoetherian Y] (d : ℕ)
    (M : DerivedCategory.Plus
      (Sheaf (affineTraceTower Y d).smallEtaleTopology (ModuleCat.{u + 1} A))) :
    ordinaryCompactComparison A Y d M =
      (Etale.affineTraceUnboundedCompactComparison A Y d).app M.obj := by
  apply Iso.ext
  change (Etale.affineTracePlusCompatibility A Y d).inv.app M ≫
    DerivedCategory.Plus.ι.map
      ((Etale.affineTraceCompactSupportComparison A Y d).hom.app M) ≫
    (Etale.rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A)
      (affineTraceProjection Y d)).hom.app M =
    (Etale.affineTraceUnboundedCompactComparison A Y d).hom.app
      (DerivedCategory.Plus.ι.obj M)
  apply (cancel_epi ((Etale.affineTracePlusCompatibility A Y d).hom.app M)).mp
  simp only [Iso.hom_inv_id_app_assoc]
  exact (Etale.affineTraceUnboundedCompactComparison_restriction A Y d M).symm

/-- The ordinary last-line contraction agrees with the last ordered-adjunction step.
There is no change of sites or pro-etale realization in this equality.
Source: projection-purity agreement, final canonical-reassociation paragraph.
(blueprint: lem-pur-affine-ordered-ordinary-counit-step).

Proof: factor ordinaryTensorCoordinatesRaw through ordinaryOrderedRightCoordinates.
Use affineTower_projection_eq to transport both coordinate ranks to the affine-trace
model. Put m = d+1. Let E_m be ordinaryOrderedRightCoordinates after that transport,
and let beta_J be sourceCoordinates followed by rightComparison inverse. The source
square to establish is etaleSourceReassociation.hom followed by beta_J and the line
right functor applied to E_m.hom equals E_(m+1).hom. Expand ordinarySourceIso and the successor
clause of ordinarySourceDescent;
normalized_source_descent identifies the latter with the normalized tensor descent.
Tensor pullback associativity and orderedTateCoefficientComposition identify the
successor source map with etaleSourceReassociation, the line sourceCoordinates, and
the line right functor applied to the preceding source map. Naturality of the line
counit commutes that preceding source map past contraction. Replace
ordinaryCompactComparison by affineTraceUnboundedCompactComparison using its
bounded-below restriction theorem. Expand its successor clause and cancel the
line-to-standing support comparison and the ordinary compact-support compositor.
The remaining map is affineTraceLeft at d+1 applied to the line counit, exactly
orderedCounitStep. All transports are along equalities of the recursive towers;
zero objects, empty schemes, and zero coefficients require no separate choice. -/
theorem ordinaryEtaleCounitStep_coordinates
    (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (Ke : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y)
    (hKe : etaleFiniteTor (AffineLinePurity.Ring P) Y Ke) (d : ℕ) :
    letI : IsNoetherian Y := tower_noetherian P Y aY 0
    ordinaryEtaleCounitStep P Y aY Ke d ≫
        (ordinaryTensorCoordinates P Y aY Ke hKe (d + 1)).hom =
      (ordinaryTensorCoordinates P Y aY Ke hKe (d + 2)).hom ≫
        orderedCounitStep P Y aY Ke (d + 1) := by
  sorry


end AlgebraicGeometry.ProEtale.AffineOrderedIntegration
