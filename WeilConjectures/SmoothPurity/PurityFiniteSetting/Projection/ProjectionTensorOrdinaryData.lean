/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Projection.ProjectionPurityCoordinates
public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedIntegrationData
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.SmoothPurityMap
public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.FiniteSiteCoordinates

/-! # Ordinary coefficient coordinates for the projection tensor calculation

Source: projection purity agreement, coefficient tensor calculation.
(blueprint: def-pur-projection-tensor-ordinary-data)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting
open ProEtale ProEtale.AffineSpacePurity ProEtale.VectorIntegrationSite

/-- Coefficient integration in ordinary pullback-first tensor coordinates.
This uses the actual inverse projection and trace, including the degree-zero
unit comparison. Source: the coefficient projection formula.
(blueprint: def-pur-projection-tensor-ordinary-data) -/
def ordinaryCoefficientTrace (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (W : Etale.DerivedCategoryModule A X)
    (t : (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj W ⟶
      Etale.ordinaryFiniteUnit A Y) (H : Etale.DerivedCategoryModule A Y) :=
  (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
      (((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A) X).hom.app
        ((Etale.ordinaryFinitePullback A f).obj H)).app W) ≫
    ((inv (Etale.projectionMap (ModuleCat.{u + 1} A) f)).app W).app H ≫
    ((Etale.derivedTensor (ModuleCat.{u + 1} A) Y).map
      (t ≫ (smoothPurityUnitIso A Y).hom)).app H ≫
    (Etale.derivedTensorLeftUnitor (ModuleCat.{u + 1} A) Y H).hom

/-- The comparison image of the ordered ordinary coefficient adjunct, with the
actual comparison-adjunction unit and presentation isomorphism. No standing
proetale exceptional transpose is used in this construction.
Source: the bounded comparison Hom chain.
(blueprint: def-pur-projection-tensor-ordinary-data) -/
def projectionCoefficientMate
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of F.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    (K : ProEtale.AffineSpacePurity.C (projectionSetting F C E n).Coefficient Y)
    (H : Etale.DerivedCategoryModule (projectionSetting F C E n).Coefficient Y)
    (e : (comparison (projectionSetting F C E n).Coefficient Y).obj H ≅ K) (d : ℕ) :=
  let P := projectionSetting F C E n
  letI := (projection_geometry Y d).2
  letI : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType aY
  let p := iteratedAffineLineProj Y d
  let W := ProEtale.AffineOrderedIntegration.etaleCoefficient P Y d
  (comparison P.Coefficient (iteratedAffineLine Y d)).map
      ((Etale.rightDerivedUpperShriekAdjunction P.Coefficient p).homEquiv _ _
        (ordinaryCoefficientTrace P.Coefficient p W
          (ProEtale.AffineOrderedIntegration.ordinaryTrace P Y aY d) H)) ≫
    (comparison P.Coefficient (iteratedAffineLine Y d)).map
      ((Etale.rightDerivedUpperShriek P.Coefficient p).map
        ((derivedComparisonAdjunction (ModuleCat.{u + 1} P.Coefficient) Y).unit.app H ≫
          (comparisonLowerStar (ModuleCat.{u + 1} P.Coefficient) Y).rightDerivedFunctor.map
            e.hom)) ≫
    ((P.smoothPurityExceptionalComparison p).app K).inv

/-- The inverse root transition on the ordered ordinary affine coefficient.
Source: normalized finite Tate descent, in the direction from the diagonal
exponent to the integration exponent.
(blueprint: def-pur-projection-tensor-ordinary-data) -/
def projectionCoefficientRootIso
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (T : Scheme.{u}) (aT : T ⟶ Spec (.of F.k)) (d : ℕ) :=
  let P := projectionSetting F C E n
  (baseExponentComparison C.l E n T (AffineLinePurity.primeUnit P T aT)
    n (n + 1) (Nat.le_succ n) P.diagonalExponent_annihilates (annihilates P) d).symm

end WeilConjectures.PurityFiniteSetting
