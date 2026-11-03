/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineLineEvaluation.AffineLineCompositeTranspose
public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedEtaleSourceReassociation
import all WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineRankOneSourceRealization
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.AffineDiagonalTensorCoordinates
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonOpenTensorCoherence
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.Dnc.ComparisonPullbackDerivedCoherence
import all WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteUnitPullbackNormalization
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionMonoidal
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryMonoidal

/-! # Realization of ordered-source reassociation

Source: projection-purity agreement, final paragraph: canonical tensor reassociations.
(blueprint: lem-pur-affine-ordered-source-reassociation-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option Elab.async false
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
set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2
  AffineSpacePurity.C._proof_1 AffineSpacePurity.C._proof_2
attribute [local instance high] GrothendieckTopology.W.monoidal
attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory
attribute [local instance 200000] sheafIsAbelian
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] Etale.sheafBraidedCategory
attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
  Scheme.finiteEtaleTateLine DerivedCategory.TStructure.t
  Functor.leftDerivedFunctor Functor.mapDerivedCategory DerivedCategory.singleFunctors
attribute [local semireducible] projectionSourceObject proSourceObject
set_option allowUnsafeReducibility true in
attribute [local implicit_reducible] projectionSourceObject proSourceObject
  coefficient etaleCoefficient
  shiftedLine action AffineLinePurity.etaleCoefficient AffineLinePurity.etaleSource
open CategoryTheory.MonoidalCategory
set_option allowUnsafeReducibility true in
attribute [local implicit_reducible] id Etale.ordinaryFiniteDerivedCategoryInstance
  Etale.ordinaryFinitePullback Etale.ordinaryFiniteTwistedPullback
  Sheaf.monoidalCategory Etale.derivedTensor derivedTensor
  Etale.ordinaryFiniteUnit Etale.ordinaryFiniteConstant
  Etale.ordinaryFiniteDegreeZero Etale.ordinaryFiniteSingleFunctor
  Etale.ordinaryFiniteTensor Etale.derivedTensorRight Etale.derivedTensorRightFunctor
  Etale.affineLinearBaseCoefficient VectorIntegrationSite.unit
  curriedTensor AffineLinePurity.proSourceObject ordinarySourceObject
  VectorIntegrationSite.comparison constantSheaf
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
  Etale.sheafMonoidalCategory Etale.sheafBraidedCategory
  ProEtale.sheafMonoidalCategory ProEtale.sheafBraidedCategory
set_option allowUnsafeReducibility true in
attribute [local reducible] etaleCategory proCategory VectorIntegrationSite.comparison
  Etale.ordinaryFinitePullback AffineSpacePurity.inverseImage
attribute [local irreducible] Functor.mapDerivedCategoryOplaxMonoidal

set_option maxHeartbeats 800000 in
-- Normalize the cached derived-category structures.
/-- Pullback of the comparison-origin ordered coefficient, using the actual site
comparison and normalized ordinary finite coefficient pullback. -/
def coefficient_pullback_iso
    (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hA : (N : A) = 0)
    (t : Etale.OrdinaryFiniteTwistTransport A N hA) {X Y : Scheme.{u}}
    (f : X ⟶ Y) (hY : IsUnit (N : Γ(Y, ⊤))) (n : ℕ) :
    (inverseImage A f).obj ((comparison A Y).obj
      (Etale.affineLinearBaseCoefficient A N hA Y n)) ≅
      (comparison A X).obj (Etale.affineLinearBaseCoefficient A N hA X n) :=
  ((pullback A f).app (Etale.affineLinearBaseCoefficient A N hA Y n)).symm ≪≫
    (comparison A X).mapIso
      (Etale.vectorIntegrationBaseCoefficientPullback A N hA t f hY n)

set_option maxHeartbeats 800000 in
-- Normalize the cached derived-category structures.
/-- Pullback of the shifted comparison-origin finite Tate line. -/
def line_pullback_iso
    (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hA : (N : A) = 0)
    (t : Etale.OrdinaryFiniteTwistTransport A N hA) {X Y : Scheme.{u}}
    (f : X ⟶ Y) (hY : IsUnit (N : Γ(Y, ⊤))) :
    (inverseImage A f).obj ((comparison A Y).obj
      ((Etale.ordinaryFiniteLine A N hA Y)⟦(2 : ℤ)⟧)) ≅
      (comparison A X).obj ((Etale.ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧) :=
  ((pullback A f).app ((Etale.ordinaryFiniteLine A N hA Y)⟦(2 : ℤ)⟧)).symm ≪≫
    (comparison A X).mapIso (Etale.ordinaryFiniteShiftedLinePullback A N hA t f hY)

set_option maxHeartbeats 800000 in
-- Normalize the cached derived-category structures.
/-- The ordered coefficient action commutes with inverse image.

Source: projection-purity agreement, final canonical-reassociation paragraph.
Proof: induct on the rank. At rank zero, normalize the constant finite coefficient
pullback against the derived monoidal unit and use right-unitor preservation.
At a successor, expand both recursive actions. Tensor compatibility of the site
comparison identifies the pullback of the ordered coefficient successor with
pullback of its two factors. Oplax associativity moves the pullback tensorator
across the associator; naturality moves the induction hypothesis through the last
line factor. The remaining last-line map is the normalized shifted Tate pullback.
Compose these equalities and cancel the inverse tensor comparisons. This proof
uses the actual constructed unit and line maps, so it makes no choice of orientation.
(blueprint: lem-pur-ordered-coefficient-action-pullback).
-/
theorem coefficient_action_pullback
    (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hA : (N : A) = 0)
    (t : Etale.OrdinaryFiniteTwistTransport A N hA) {X Y : Scheme.{u}}
    (f : X ⟶ Y) (hY : IsUnit (N : Γ(Y, ⊤))) (M : C A Y) (n : ℕ) :
    (inverseImage A f).mapIso (coefficientActionComparison A N hA Y M n) ≪≫
        actionPullbackIso
          ((tensor A Y).flip.obj
            ((comparison A Y).obj ((Etale.ordinaryFiniteLine A N hA Y)⟦(2 : ℤ)⟧)))
          ((tensor A X).flip.obj
            ((comparison A X).obj ((Etale.ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧)))
          (inverseImage A f)
          (fun J ↦ inverseImageTensorIso A f J
            ((comparison A Y).obj ((Etale.ordinaryFiniteLine A N hA Y)⟦(2 : ℤ)⟧)) ≪≫
              tensorIso A X (Iso.refl _) (line_pullback_iso A N hA t f hY)) M n =
      inverseImageTensorIso A f M
        ((comparison A Y).obj (Etale.affineLinearBaseCoefficient A N hA Y n)) ≪≫
        tensorIso A X (Iso.refl _) (coefficient_pullback_iso A N hA t f hY n) ≪≫
        coefficientActionComparison A N hA X ((inverseImage A f).obj M) n := by
  sorry

end AlgebraicGeometry.ProEtale.AffineOrderedIntegration
