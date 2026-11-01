/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedEvaluationCoordinates
public import WeilConjectures.AlgebraicGeometry.AffineLineEvaluation.AffineLineCompositeTranspose

/-! # Recursion of the ordinary counit coordinates

Source: projection-purity agreement, final paragraph: normalized last-line evaluation.
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

/-- The ordinary tensor-source coordinates with no pro-etale source realization inserted.
Every factor is prescribed by the standing compactification and the ordinary tower.
Source: projection-purity agreement, final paragraph, site transport.
(blueprint: def-pur-affine-ordered-supported-tensor-coordinates). -/
def supportedTensorCoordinates
    (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) [IsNoetherian Y] (aY : Y ⟶ Spec (.of P.field.k))
    (Ke : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y)
    (hKe : etaleFiniteTor (AffineLinePurity.Ring P) Y Ke) (d : ℕ)
    (hJ : DerivedCategory.TStructure.t.plus (sourceEtale P Y Ke d)) :
    letI := (projection_geometry Y d).2
    (rightDerivedLowerShriek (ModuleCat.{u + 1} (AffineLinePurity.Ring P))
      (iteratedAffineLineProj Y d)).obj
      ((comparison (AffineLinePurity.Ring P) (iteratedAffineLine Y d)).obj
        (sourceEtale P Y Ke d)) ≅
    (comparison (AffineLinePurity.Ring P) Y).obj
      ((Etale.affineTraceLeft (AffineLinePurity.Ring P) Y d).obj
        ((Etale.affineTraceRight (AffineLinePurity.Ring P) (exponent P)
          (annihilates P) Y d).obj Ke)) := by
  letI := (projection_geometry Y d).2
  exact (compactSupportSiteComparison (AffineLinePurity.Ring P)
      (compactification Y d)).app ⟨_, hJ⟩ ≪≫
    (comparison (AffineLinePurity.Ring P) Y).mapIso
      ((Etale.rightDerivedLowerShriekIso (AffineLinePurity.Ring P)
        (compactification Y d)).app (sourceEtale P Y Ke d) ≪≫
        ordinaryTensorCoordinates P Y aY Ke hKe d)

/-- Separate the source realization from the source-independent support coordinates.
Source: the definition of the ordered counit coordinates.
(blueprint: def-pur-affine-ordered-supported-tensor-coordinates).
Proof: expand both displayed coordinate isomorphisms; their factors coincide. -/
theorem orderedCounitCoordinates_factor
    (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) [IsNoetherian Y] (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (AffineLinePurity.Ring P) Y)
    (Ke : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y)
    (hKe : etaleFiniteTor (AffineLinePurity.Ring P) Y Ke)
    (eK : (comparison (AffineLinePurity.Ring P) Y).obj Ke ≅ K.obj) (d : ℕ) :
    orderedCounitCoordinates P Y aY K Ke hKe eK d =
      (AffineLineEvaluation.support P aY (iteratedAffineLineProj Y d)).mapIso
        (sourceRealization P Y K.obj Ke eK d).symm ≪≫
      supportedTensorCoordinates P Y aY Ke hKe d
        (source_applicability P Y aY K Ke hKe eK d).2.1.1.1 := by
  rfl

end AlgebraicGeometry.ProEtale.AffineOrderedIntegration
