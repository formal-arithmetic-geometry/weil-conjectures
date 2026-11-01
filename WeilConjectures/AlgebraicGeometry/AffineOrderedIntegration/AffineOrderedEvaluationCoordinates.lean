/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedCounitData

/-! # Ordinary counit coordinates for ordered affine evaluations

Source: current blueprint, projection-purity agreement proof, final paragraph.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.ProEtale.AffineOrderedIntegration
open AffineSpacePurity AffineLinePurity VectorIntegrationSite

attribute [local implicit_reducible] affineTraceTower affineTraceProjection
  iteratedAffineLine iteratedAffineLineProj

/-- The two recursive coordinate projections have identical schemes and arrows.
Source: the recursive definitions of the affine towers.
(blueprint: def-pur-affine-ordered-evaluation-coordinates).
Proof: both start with the identity. Both successor operations apply the same affine
line construction and compose its projection with the preceding arrow. Apply congrArg
to that operation and the induction hypothesis. -/
theorem affineTower_projection_eq (Y : Scheme.{u}) (d : ℕ) :
    (⟨affineTraceTower Y d, affineTraceProjection Y d⟩ : Σ X : Scheme.{u}, X ⟶ Y) =
      ⟨iteratedAffineLine Y d, iteratedAffineLineProj Y d⟩ := by
  induction d with
  | zero => rfl
  | succ d ih =>
    exact congrArg (fun q : Σ X : Scheme.{u}, X ⟶ Y ↦
      (⟨AffineSpace PUnit.{u + 1} q.1,
        (AffineSpace PUnit.{u + 1} q.1 ↘ q.1) ≫ q.2⟩ : Σ X : Scheme.{u}, X ⟶ Y)) ih

/-- Ordinary tensor coordinates before transporting the identical affine towers.
Source: the canonical ordinary ordered-source descent.
(blueprint: def-pur-affine-ordered-evaluation-coordinates). -/
def ordinaryTensorCoordinatesRaw (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) [IsNoetherian Y] (aY : Y ⟶ Spec (.of P.field.k))
    (Ke : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y)
    (hKe : etaleFiniteTor (AffineLinePurity.Ring P) Y Ke) (d : ℕ) :
    (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (AffineLinePurity.Ring P))
      (affineTraceProjection Y d)).obj
      (ordinarySourceObject (AffineLinePurity.Ring P) (affineTraceProjection Y d)
        (Etale.affineLinearBaseCoefficient (AffineLinePurity.Ring P) (exponent P)
          (annihilates P) (affineTraceTower Y d) d) Ke) ≅
      (Etale.affineTraceLeft (AffineLinePurity.Ring P) Y d).obj
        ((Etale.affineTraceRight (AffineLinePurity.Ring P) (exponent P)
          (annihilates P) Y d).obj Ke) := by
  let A := AffineLinePurity.Ring P
  let W := fun X : Scheme.{u} ↦
    Etale.affineLinearBaseCoefficient A (exponent P) (annihilates P) X d
  let e : ordinarySourceObject A (affineTraceProjection Y d)
      (W (affineTraceTower Y d)) Ke ≅
        (Etale.affineTraceRight A (exponent P) (annihilates P) Y d).obj Ke := by
    unfold ordinarySourceObject
    exact Etale.ordinaryFiniteTensorRightMapIso A (affineTraceTower Y d)
      ((Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
        (affineTraceProjection Y d)).app Ke) (Iso.refl _) ≪≫
      (ordinarySourceIso P Y aY Ke d).symm
  exact (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (affineTraceProjection Y d)).mapIso e ≪≫
    (ordinaryCompactComparison A Y d ⟨_, ordinarySource_plus P Y aY Ke hKe d⟩).symm

/-- Supported ordinary tensor sources in the canonical ordered-adjunction coordinates.
The only endpoint transport identifies the two identical recursive affine towers.
Source: projection-purity agreement, final paragraph, canonical reassociations.
(blueprint: def-pur-affine-ordered-evaluation-coordinates). -/
def ordinaryTensorCoordinates (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) [IsNoetherian Y] (aY : Y ⟶ Spec (.of P.field.k))
    (Ke : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y)
    (hKe : etaleFiniteTor (AffineLinePurity.Ring P) Y Ke) (d : ℕ) :
    (ordinaryLower P Y d).obj (sourceEtale P Y Ke d) ≅
      (Etale.affineTraceLeft (AffineLinePurity.Ring P) Y d).obj
        ((Etale.affineTraceRight (AffineLinePurity.Ring P) (exponent P)
          (annihilates P) Y d).obj Ke) := by
  let A := AffineLinePurity.Ring P
  let W := fun X : Scheme.{u} ↦
    Etale.affineLinearBaseCoefficient A (exponent P) (annihilates P) X d
  let typ := fun q : {q : Σ X : Scheme.{u}, X ⟶ Y // HasCompactification q.2} ↦
    letI := q.property
    (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) q.val.2).obj
      (ordinarySourceObject A q.val.2 (W q.val.1) Ke) ≅
        (Etale.affineTraceLeft A Y d).obj
          ((Etale.affineTraceRight A (exponent P) (annihilates P) Y d).obj Ke)
  have ht : typ ⟨⟨affineTraceTower Y d, affineTraceProjection Y d⟩, inferInstance⟩ =
      typ ⟨⟨iteratedAffineLine Y d, iteratedAffineLineProj Y d⟩,
        (projection_geometry Y d).2⟩ :=
    congrArg typ (Subtype.ext (affineTower_projection_eq Y d))
  apply cast ht
  exact ordinaryTensorCoordinatesRaw P Y aY Ke hKe d

end AlgebraicGeometry.ProEtale.AffineOrderedIntegration
