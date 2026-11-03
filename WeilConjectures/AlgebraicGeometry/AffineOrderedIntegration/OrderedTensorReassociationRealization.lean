/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineLineEvaluation.AffineLineCompositeTranspose
public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.OrderedCoefficientActionPullback
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
/-- Tensor-source reassociation before converting ordered coefficient action. -/
def tensor_source_reassociation
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X B Y : Scheme.{u}} (f : X ⟶ B) (g : B ⟶ Y)
    (V : Etale.DerivedCategoryModule A B) (V' L : Etale.DerivedCategoryModule A X)
    (T : C A X)
    (eV : (inverseImage A f).obj ((comparison A B).obj V) ≅ (comparison A X).obj V')
    (eL : (comparison A X).obj L ≅ T) (K : C A Y) :
    ((inverseImage A (f ≫ g)).obj K) ⊗ (comparison A X).obj (V' ⊗ L) ≅
      (inverseImage A f).obj (((inverseImage A g).obj K) ⊗ (comparison A B).obj V) ⊗ T :=
  ((tensor A X).obj ((inverseImage A (f ≫ g)).obj K)).mapIso
      (tensorComparison A X V' L) ≪≫
    (α_ ((inverseImage A (f ≫ g)).obj K)
      ((comparison A X).obj V') ((comparison A X).obj L)).symm ≪≫
    tensorIso A X
      (tensorIso A X ((inverseImageComp A f g).app K) eV.symm ≪≫
        (inverseImageTensorIso A f ((inverseImage A g).obj K)
          ((comparison A B).obj V)).symm) eL

set_option maxHeartbeats 800000 in
-- Normalize the cached derived-category structures.
/-- Ordinary binary source reassociation from pullback composition and tensor pullback. -/
def ordinary_binary_reassociation
    (A : Type (u + 1)) [CommRing A]
    {X B Y : Scheme.{u}} (f : X ⟶ B) (g : B ⟶ Y)
    (V : Etale.DerivedCategoryModule A B) (V' : Etale.DerivedCategoryModule A X)
    (eV : (Etale.ordinaryFinitePullback A f).obj V ≅ V')
    (Ke : Etale.DerivedCategoryModule A Y) :
    ((Etale.ordinaryFinitePullback A (f ≫ g)).obj Ke) ⊗ V' ≅
      (Etale.ordinaryFinitePullback A f).obj
        (((Etale.ordinaryFinitePullback A g).obj Ke) ⊗ V) :=
  Etale.ordinaryFiniteTensorRightMapIso A X
      ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g).app Ke) eV.symm ≪≫
    (Etale.ordinaryFiniteTensorPullback A f
      ((Etale.ordinaryFinitePullback A g).obj Ke) V).symm

set_option maxHeartbeats 800000 in
-- Normalize the cached derived-category structures.
/-- Ordinary source reassociation with one final shifted line factor attached. -/
def ordinary_tensor_reassociation
    (A : Type (u + 1)) [CommRing A]
    {X B Y : Scheme.{u}} (f : X ⟶ B) (g : B ⟶ Y)
    (V : Etale.DerivedCategoryModule A B)
    (V' L J : Etale.DerivedCategoryModule A X)
    (eV : (Etale.ordinaryFinitePullback A f).obj V ≅ V') (eL : L ≅ J)
    (Ke : Etale.DerivedCategoryModule A Y) :
    ((Etale.ordinaryFinitePullback A (f ≫ g)).obj Ke) ⊗ (V' ⊗ L) ≅
      (Etale.ordinaryFinitePullback A f).obj
        (((Etale.ordinaryFinitePullback A g).obj Ke) ⊗ V) ⊗ J :=
  (α_ ((Etale.ordinaryFinitePullback A (f ≫ g)).obj Ke) V' L).symm ≪≫
    Etale.ordinaryFiniteTensorRightMapIso A X
      (ordinary_binary_reassociation A f g V V' eV Ke) eL

set_option maxHeartbeats 800000 in
-- Normalize the cached derived-category structures.
/-- Realization commutes with binary source reassociation and a final line factor.

Source: projection-purity agreement, final canonical-reassociation paragraph.
Proof: first prove the binary square by expanding realizedTensorComparison. The
site comparison tensor square moves the tensorator past the comparison pullback;
naturality moves the coefficient isomorphism eV and the realization eK. The derived
comparison pullback composition law identifies the remaining two-factor pullback
with pullback along the composite. These give the binary reassociation square.
Apply oplax associativity to comparison to attach L, using naturality of the binary
square under right tensoring. Finally use naturality of realizedTensorComparison
in the coefficient isomorphism eL to replace L by J. The ordinary composite is the
definition of ordinary_tensor_reassociation; all arrows are canonical isomorphisms.
(blueprint: lem-pur-ordered-tensor-reassociation-realization).
-/
theorem realized_tensor_reassociation
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X B Y : Scheme.{u}} (f : X ⟶ B) (g : B ⟶ Y)
    (V : Etale.DerivedCategoryModule A B)
    (V' L J : Etale.DerivedCategoryModule A X)
    (eV : (Etale.ordinaryFinitePullback A f).obj V ≅ V')
    (eL : L ≅ J)
    (K : C A Y) (Ke : Etale.DerivedCategoryModule A Y)
    (eK : (comparison A Y).obj Ke ≅ K) :
    let v := ((pullback A f).app V).symm ≪≫ (comparison A X).mapIso eV
    realizedTensorComparison A (f ≫ g) K Ke (V' ⊗ L) eK ≪≫
        tensor_source_reassociation A f g V V' L ((comparison A X).obj J) v
          ((comparison A X).mapIso eL) K =
      (comparison A X).mapIso (ordinary_tensor_reassociation A f g V V' L J eV eL Ke) ≪≫
        realizedTensorComparison A f
          (proSourceObject A g V K) (ordinarySourceObject A g V Ke) J
          (realizedTensorComparison A g K Ke V eK) := by
  sorry

end AlgebraicGeometry.ProEtale.AffineOrderedIntegration
