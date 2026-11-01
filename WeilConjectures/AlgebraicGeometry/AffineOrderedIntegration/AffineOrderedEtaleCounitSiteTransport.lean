/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedLineEvaluationCoordinates
public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedOrdinaryLineContraction
import all WeilConjectures.AlgebraicGeometry.Canonical.CanonicalOriginCompactSupportComposition

/-! # Site transport before ordinary tensor coordinates

Source: projection-purity agreement, final canonical-reassociation paragraph.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.ProEtale.AffineOrderedIntegration
open AffineSpacePurity AffineLinePurity VectorIntegrationSite
attribute [local semireducible] orderedSource exceptional lineSource twistAction
attribute [local implicit_reducible] orderedSource exceptional lineSource twistAction
attribute [local implicit_reducible] iteratedAffineLine iteratedAffineLineProj
  etaleCategory proCategory sourceEtale
attribute [local semireducible] sourceWitness
attribute [local implicit_reducible] sourceWitness

private theorem ambient_compositor_model
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X B Y : Scheme.{u}} (q : X ⟶ B) (f : B ⟶ Y)
    [HasCompactification q] [HasCompactification f] [HasCompactification (q ≫ f)]
    [QuasiCompact q] [QuasiCompact f] :
    Functor.whiskerLeft (comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X)
        (originCompositionAmbient A q f).hom = (originCompositionModel A q f).hom := by
  exact preimage_whiskerLeft
    (comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X)
    (originCompositionModel A q f)

/-- Site transport of the last-line contraction, before ordinary tensor coordinates.
This equality contains no higher-rank ordinary tensor coordinates.
Source: projection-purity agreement, final compact-support composition paragraph.
(blueprint: lem-pur-affine-ordered-etale-counit-site-transport).

Proof: use naturality of originCompositionAmbient to move the line witness from
total support to iterated support. Apply rankOne_source_coordinates to replace
support of that witness followed by lineEvaluationCoordinates by the fixed
chart support comparison and comparison of the ordinary line source map.
Normalize the fixed compact-support comparison to compactSupportSiteComparison.
Expand originCompositionAmbient on its retained bounded-below etale witness by
originCompositionModel, using ambient_compositor_model and Iso.ext to identify
the inverse components. The inverse compositor cancels the intermediate site
comparisons and bounded-below inclusion maps. Naturality of the preceding support
site comparison moves comparison of the ordinary line counit through that comparison.
The ordinary bounded and unbounded compact-support compositors agree on this
bounded-below source. Thus the remaining ordinary map is the total ordinary support
of etaleSourceReassociation, inverse ordinary support compositor, and support of
ordinaryLineContraction: exactly ordinaryEtaleCounitStep. Both sides use literal
Ring P, so no coefficient equivalence or change of level is needed. The proof does
not require the ordinary source-coordinate successor identity. -/
theorem etaleCounit_site_transport
    (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (Ke : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y)
    (d : ℕ)
    (H : Plus (AffineLinePurity.Ring P) (iteratedAffineLine Y (d + 1)))
    (hJ : etaleFiniteTor (AffineLinePurity.Ring P) (iteratedAffineLine Y (d + 1))
      (sourceEtale P Y Ke (d + 1)))
    (eH : (comparison (AffineLinePurity.Ring P) (iteratedAffineLine Y (d + 1))).obj
      (sourceEtale P Y Ke (d + 1)) ≅ H.obj)
    (hJnext : DerivedCategory.TStructure.t.plus (sourceEtale P Y Ke (d + 2))) :
    letI : IsNoetherian Y := tower_noetherian P Y aY 0
    letI : LocallyOfFiniteType (towerBase aY (d + 1)) := (tower_geometry aY (d + 1)).1
    letI : QuasiCompact (towerBase aY (d + 1)) := (tower_geometry aY (d + 1)).2.1
    letI : IsSeparated (towerBase aY (d + 1)) := (tower_geometry aY (d + 1)).2.2
    letI : IsNoetherian (iteratedAffineLine Y (d + 1)) :=
      tower_noetherian P Y aY (d + 1)
    (AffineLineEvaluation.support P aY (iteratedAffineLineProj Y (d + 2))).map
      ((comparison (AffineLinePurity.Ring P) (iteratedAffineLine Y (d + 2))).map
          (etaleSourceReassociation P Y aY Ke d).hom ≫
        (AffineLineEvaluation.lineWitness P (iteratedAffineLine Y (d + 1)) H.obj
          (sourceEtale P Y Ke (d + 1)) hJ eH).iso.hom) ≫
    (AffineLineEvaluation.compositor P aY (iteratedAffineLineProj Y (d + 1))
      H.obj (sourceEtale P Y Ke (d + 1)) hJ eH).inv ≫
    (AffineLineEvaluation.support P aY (iteratedAffineLineProj Y (d + 1))).map
      ((lineEvaluationCoordinates P (iteratedAffineLine Y (d + 1))
        (towerBase aY (d + 1)) H (sourceEtale P Y Ke (d + 1)) hJ eH).hom ≫
      (comparison (AffineLinePurity.Ring P) (iteratedAffineLine Y (d + 1))).map
        (orderedCounitStep P (iteratedAffineLine Y (d + 1))
          (towerBase aY (d + 1)) (sourceEtale P Y Ke (d + 1)) 0)) ≫
    (ordinarySupportCoordinates P Y Ke (d + 1) hJ.1.1.1).hom =
      (ordinarySupportCoordinates P Y Ke (d + 2) hJnext).hom ≫
        (comparison (AffineLinePurity.Ring P) Y).map
          (ordinaryEtaleCounitStep P Y aY Ke d) := by
  sorry


end AlgebraicGeometry.ProEtale.AffineOrderedIntegration
