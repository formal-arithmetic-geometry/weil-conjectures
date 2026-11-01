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

/-- Every ordinary ordered right-adjoint source has constructible finite Tor amplitude.
This transports the proved tensor-source applicability through the specified source
isomorphism, retaining the exact-versus-derived pullback comparison.
Source: projection-purity agreement, final paragraph, admissibility of every line input.
(blueprint: lem-pur-affine-ordered-right-finite-tor).

Proof: transport source_applicability along affineTower_projection_eq to the ordinary
coordinate tower. The exact-to-derived tensor comparison followed by the inverse of
ordinarySourceIso identifies that tensor source with the actual ordered right source.
The constructible finite-Tor object property is invariant under this isomorphism. -/
theorem orderedRight_finiteTor
    (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (AffineLinePurity.Ring P) Y)
    (Ke : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y)
    (hKe : etaleFiniteTor (AffineLinePurity.Ring P) Y Ke)
    (eK : (comparison (AffineLinePurity.Ring P) Y).obj Ke ≅ K.obj) (d : ℕ) :
    etaleFiniteTor (AffineLinePurity.Ring P) (affineTraceTower Y d)
      ((Etale.affineTraceRight (AffineLinePurity.Ring P) (exponent P)
        (annihilates P) Y d).obj Ke) := by
  let A := AffineLinePurity.Ring P
  let W := fun X : Scheme.{u} ↦
    Etale.affineLinearBaseCoefficient A (exponent P) (annihilates P) X d
  let Q := fun q : Σ X : Scheme.{u}, X ⟶ Y ↦
    etaleFiniteTor A q.1 (ordinarySourceObject A q.2 (W q.1) Ke)
  have hraw : Q ⟨affineTraceTower Y d, affineTraceProjection Y d⟩ :=
    (congrArg Q (affineTower_projection_eq Y d)).mpr
      (source_applicability P Y aY K Ke hKe eK d).2
  exact (Etale.DerivedCategory.constructibleFiniteTor
    (ModuleCat.{u + 1} A) (affineTraceTower Y d)).prop_of_iso
      (ordinaryOrderedRightCoordinates P Y aY Ke d) hraw

end AlgebraicGeometry.ProEtale.AffineOrderedIntegration
