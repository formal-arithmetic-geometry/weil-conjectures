/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Arrows
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
import all Mathlib.Logic.Small.Defs
import Sheaf.AlgebraicGeometry.OrdinaryFiniteUnitPullbackComparison
import Sheaf.AlgebraicGeometry.EtaleSectionUnitNormalization

/-! # Ordinary coefficient units and monoidal unit coordinates

Source: the unit identifications in the rank-zero smooth-purity orientation.
(blueprint: lem-pur-ordinary-finite-unit-coordinate-identification).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

attribute [local instance 100000] ordinaryFiniteDerivedCategoryInstance
attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
attribute [local implicit_reducible] CategoryTheory.catToReflQuiver
  ordinaryFiniteSingleFunctor ordinaryFiniteDegreeZero
  Etale.sheafMonoidalCategory Etale.sheafBraidedCategory
attribute [local instance 20002] Etale.sheafMonoidalCategory Etale.sheafBraidedCategory
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
attribute [local irreducible] upperStar lowerStar etaleLowerShriek
  Functor.mapDerivedCategory Functor.rightDerivedFunctor Functor.leftDerivedFunctor
  leftDerivedUpperStarIsoMapDerivedCategory

private theorem single_unit_hom
    (M : Type v) [Category.{u + 1} M] [Abelian M]
    [IsGrothendieckAbelian.{u + 1} M] [MonoidalCategory M] [MonoidalPreadditive M]
    [SymmetricCategory M] [MonoidalClosed M] [Abelian.HasFunctorialFlatResolution M]
    (S : Scheme.{u}) :
    (singleFunctorObjUnitIso M S).hom = 𝟙 _ := by
  have h := (singleFunctorObjUnitIso M S).inv_hom_id
  rwa [singleFunctorObjUnitIso_inv, Category.id_comp] at h

private theorem constant_unit_pullback_hom
    (M : Type v) [Category.{u + 1} M] [Abelian M]
    [IsGrothendieckAbelian.{u + 1} M] [MonoidalCategory M] [MonoidalPreadditive M]
    [SymmetricCategory M] [MonoidalClosed M] [Abelian.HasFunctorialFlatResolution M]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (constantSinglePullbackIso M f (𝟙_ M)).hom =
      (leftDerivedUpperStarUnitIso M f).hom := by
  have h := (constantUnitPullback_unit M f).symm
  simp only [single_unit_hom, CategoryTheory.Functor.map_id, Category.id_comp] at h
  exact (Category.comp_id _).symm.trans h

/-- The ordinary constant coefficient pullback is the monoidal unit pullback in
its canonical degree-zero coordinates.
Source: the coefficient-unit identifications in the third arrow of
sk-prop-sp-orientation.proof.md, and constantUnitPullback_unit.
(blueprint: lem-pur-ordinary-finite-unit-coordinate-identification).

Proof: singleFunctorObjUnitIso has identity inverse and hence identity hom.
For an arbitrary coefficient category, substitute these identities into the proved
constant-unit pullback square and cancel the two identity maps. The existing
ordinary finite constant-pullback comparison identifies its component with that
generic component at ModuleCat A. Specialize the generic identity and compose
these two equalities. The construction is valid for every commutative coefficient
ring, including the zero ring, and every scheme morphism, including empty schemes. -/
theorem ordinaryFiniteUnitPullback_eq_unitCoordinates
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (ordinaryFiniteUnitPullback A f).hom =
      (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) f).hom := by
  exact (ordinaryFiniteUnitPullback_hom_eq_constant A f).trans
    (constant_unit_pullback_hom (ModuleCat.{u + 1} A) f)

end AlgebraicGeometry.Etale.FiniteSmoothPurity
