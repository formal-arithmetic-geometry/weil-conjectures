/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SfGraphProjectionData
public import WeilConjectures.CategoryTheory.BrownCohomologicalRepresentabilityUniverseTransfer
public import WeilConjectures.CategoryTheory.CompactGenerationEquivalence
public import WeilConjectures.CategoryTheory.DerivedModuleDirectSums
public import WeilConjectures.CategoryTheory.TriangulatedEquivalenceTransfer
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
import WeilConjectures.AlgebraicGeometry.SfGraphCompositionTailProjection
import WeilConjectures.AlgebraicGeometry.SfGraphWordProjectionSquare

/-! # Forward projection square for the specified graph compositor
-/

@[expose] public section
set_option autoImplicit false
universe u u'
open CategoryTheory CategoryTheory.Limits MonoidalCategory
attribute [local instance high] SymmetricCategory.toBraidedCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local instance 20000] Etale.sheafBraidedCategory

set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] projectionMapOfCompactification derivedTensor
  sfCompactProjection sfGraphPresentationComparison
  sfGraphWordProjection sfCompositionGraphPresentation sfGraphCompositionTailIso
  sfGraphCompactificationComparison sfGraphCompactSupportCompIso
  Functor.mapDerivedCategory Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  DerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian
attribute [local implicit_reducible] EtaleGraphPresentation.functor
  derivedTensorRightDerivedLowerShriek
  rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar

/-- The specified graph compositor intertwines the forward compactification projections,
for arbitrary schemes and unbounded derived objects. -/
theorem sfEtaleCompactProjectionForward_composition
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (cf : Compactification f) (cg : Compactification g)
    (ch : Compactification (f ≫ g))
    (M : DerivedCategoryModule A X) (K : DerivedCategoryModule A Z) :
    let B := ModuleCat.{u + 1} A
    let F := rightDerivedLowerShriekOfCompactification B cf
    let G := rightDerivedLowerShriekOfCompactification B cg
    let T := derivedTensor B X
    let U := derivedTensor B Z
    let E := sfGraphCompactSupportCompIso A f g cf cg ch
    (U.map (E.hom.app M)).app K ≫
      sfCompactProjection A cg (F.obj M) K ≫
        G.map (sfCompactProjection A cf M ((upperStar B g).leftDerivedFunctor.obj K)) =
      sfCompactProjection A ch M K ≫
        E.hom.app ((T.obj M).obj ((upperStar B (f ≫ g)).leftDerivedFunctor.obj K)) ≫
        G.map (F.map ((T.obj M).map ((leftDerivedUpperStarComp B f g).hom.app K))) := by
  dsimp only
  have h₁ := sfGraphCompositionTailIso_projection A f g cf cg ch M K
  have h₀ := sfGraphCompactificationComparison_projection A ch
    (sfCompositionGraphPresentation f g cg ch) M K
  rw [sfGraphCompactSupportCompIso_factor]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [h₁, reassoc_of% h₀]

end AlgebraicGeometry.Etale
