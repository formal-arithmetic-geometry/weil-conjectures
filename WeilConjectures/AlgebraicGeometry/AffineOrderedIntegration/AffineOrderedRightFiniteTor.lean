/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedEvaluationCoordinates

/-! # Finite-Tor admissibility of the ordered right source

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

/-- Explicit tensor-source coordinates for the actual ordered right adjoint.
Source: canonical ordered source descent, followed by the exact-versus-derived
pullback comparison (blueprint: lem-pur-affine-ordered-right-finite-tor). -/
def ordinaryOrderedRightCoordinates
    (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    (Ke : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y) (d : ℕ) :
    ordinarySourceObject (AffineLinePurity.Ring P) (affineTraceProjection Y d)
      (Etale.affineLinearBaseCoefficient (AffineLinePurity.Ring P) (exponent P)
        (annihilates P) (affineTraceTower Y d) d) Ke ≅
      (Etale.affineTraceRight (AffineLinePurity.Ring P) (exponent P)
        (annihilates P) Y d).obj Ke := by
  unfold ordinarySourceObject
  exact Etale.ordinaryFiniteTensorRightMapIso (AffineLinePurity.Ring P)
    (affineTraceTower Y d)
    ((Etale.leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} (AffineLinePurity.Ring P))
      (affineTraceProjection Y d)).app Ke) (Iso.refl _) ≪≫
    (ordinarySourceIso P Y aY Ke d).symm

end AlgebraicGeometry.ProEtale.AffineOrderedIntegration
