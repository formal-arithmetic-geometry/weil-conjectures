/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedIntegrationData

/-! # Ordinary source reassociation on the iterated affine tower -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.ProEtale.AffineOrderedIntegration
open AffineSpacePurity AffineLinePurity VectorIntegrationSite

/-- Reassociate the total ordinary tensor source into the last chart-line source.
This uses tensor associativity, the pullback compositor, and the normalized Tate
pullbacks, without making any choices of isomorphisms.
Source: projection-purity agreement, final paragraph, canonical reassociations.
(blueprint: def-pur-affine-ordered-etale-source-reassociation). -/
def etaleSourceReassociation
    (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    (Ke : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y) (d : ℕ) :
    sourceEtale P Y Ke (d + 2) ≅
      AffineLinePurity.etaleSource P.coefficients.l P.extension (P.level - 1)
        (iteratedAffineLine Y (d + 1)) P.level (annihilates P)
        (sourceEtale P Y Ke (d + 1)) := by
  let A := AffineLinePurity.Ring P
  let B := iteratedAffineLine Y (d + 1)
  let X := iteratedAffineLine Y (d + 2)
  let q := lastProjection Y (d + 1)
  let f := iteratedAffineLineProj Y (d + 1)
  let V := Etale.affineLinearBaseCoefficient A (exponent P) (annihilates P) B (d + 1)
  let V' := Etale.affineLinearBaseCoefficient A (exponent P) (annihilates P) X (d + 1)
  let L := (Etale.ordinaryFiniteLine A (exponent P) (annihilates P) X)⟦(2 : ℤ)⟧
  have hB : IsUnit (exponent P : Γ(B, ⊤)) :=
    affineTracePullbackInvertible (exponent P) f (exponentUnit P Y aY)
  let eV : (Etale.ordinaryFinitePullback A q).obj V ≅ V' :=
    Etale.vectorIntegrationBaseCoefficientPullback A (exponent P) (annihilates P)
      (transport P) q hB (d + 1)
  let eL : AffineLinePurity.etaleCoefficient P.coefficients.l P.extension
      (P.level - 1) B P.level (annihilates P) ≅ L :=
    eqToIso (AffineLinePurity.etaleCoefficient_eq P.coefficients.l P.extension
      (P.level - 1) B P.level (annihilates P)) ≪≫
    Etale.ordinaryFiniteShiftedLinePullback A (exponent P) (annihilates P)
      (transport P) (ProjectiveLine.affineChart B)
      (affineTraceProjectiveInvertible (exponent P) B hB)
  let e : ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj
      ((Etale.ordinaryFinitePullback A (q ≫ f)).obj Ke)).obj V' ≅
      (Etale.ordinaryFinitePullback A q).obj (sourceEtale P Y Ke (d + 1)) := by
    unfold sourceEtale AffineOrderedIntegration.etaleCoefficient
      AffineLinePurity.ordinarySourceObject
    exact Etale.ordinaryFiniteTensorRightMapIso A X
      ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) q f).app Ke) eV.symm ≪≫
      (Etale.ordinaryFiniteTensorPullback A q
        ((Etale.ordinaryFinitePullback A f).obj Ke) V).symm
  unfold sourceEtale AffineOrderedIntegration.etaleCoefficient
      AffineLinePurity.ordinarySourceObject at e
  unfold sourceEtale AffineOrderedIntegration.etaleCoefficient
    AffineLinePurity.etaleSource ordinarySourceObject
  exact (Etale.derivedTensorAssociator (ModuleCat.{u + 1} A) X
      ((Etale.ordinaryFinitePullback A (q ≫ f)).obj Ke) V' L).symm ≪≫
    Etale.ordinaryFiniteTensorRightMapIso A X e eL.symm

end AlgebraicGeometry.ProEtale.AffineOrderedIntegration
