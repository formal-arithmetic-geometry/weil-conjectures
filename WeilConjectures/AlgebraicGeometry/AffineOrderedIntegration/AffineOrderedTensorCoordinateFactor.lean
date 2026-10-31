/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedRightFiniteTor

/-! # Factorization of the ordinary tensor coordinates

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

/-- The supported ordinary tensor coordinates factor through their explicit source iso.
Source: the canonical ordinary-source coordinates in the ordered integration argument
(blueprint: lem-pur-affine-ordered-tensor-coordinate-factor).
Proof: unfold the coordinate definitions. Their initial source isomorphisms are the
same exact-versus-derived tensor comparison followed by ordinarySourceIso inverse;
their terminal compact-support comparisons and boundedness proofs coincide. -/
theorem ordinaryTensorCoordinatesRaw_factor
    (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) [IsNoetherian Y] (aY : Y ⟶ Spec (.of P.field.k))
    (Ke : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y)
    (hKe : etaleFiniteTor (AffineLinePurity.Ring P) Y Ke) (d : ℕ) :
    ordinaryTensorCoordinatesRaw P Y aY Ke hKe d =
      (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (AffineLinePurity.Ring P))
        (affineTraceProjection Y d)).mapIso
          (ordinaryOrderedRightCoordinates P Y aY Ke d) ≪≫
      (ordinaryCompactComparison (AffineLinePurity.Ring P) Y d
        ⟨_, ordinarySource_plus P Y aY Ke hKe d⟩).symm := by
  unfold ordinaryTensorCoordinatesRaw ordinaryOrderedRightCoordinates
  rfl

end AlgebraicGeometry.ProEtale.AffineOrderedIntegration
