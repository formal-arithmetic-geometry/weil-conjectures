/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineLinePurity.AffineLinePurityCoordinateMaps
import all WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Finite.DiagonalFiniteConstantPullbackComparison

/-! # The compared coefficient unit and the native derived pullback unit -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor

attribute [-instance] AlgebraicGeometry.ProEtale.diagonalModuleSheafAbelian
  AlgebraicGeometry.ProEtale.diagonalAbSheafAbelian in
section
attribute [local instance 100000] AlgebraicGeometry.Etale.ordinaryFiniteDerivedCategoryInstance

namespace AlgebraicGeometry.ProEtale.OrderedProjectionUnit
open AffineLinePurity VectorIntegrationSite DiagonalCoefficients

attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
  HasDerivedCategory.ofIsGrothendieckAbelian
attribute [local implicit_reducible] DerivedCategory.singleFunctors
  CochainComplex.singleFunctors HomotopyCategory.singleFunctors
  Etale.ordinaryFiniteDegreeZero
  Etale.ordinaryFiniteSingleFunctor geoCartierConstant
  ProEtale.sheafMonoidalCategory Etale.sheafMonoidalCategory constantSheaf
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall HomotopyCategory

private theorem coefficient_finite_unit
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    (coefficientUnitIso (ModuleCat.{u + 1} A) X).hom =
      (finiteUnitComparison A X).hom ≫ (DerivedCategory.singleFunctorObjUnitIso
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))).hom := by
  have he : finiteSingleComparison A X =
      (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategorySingleFunctor 0 :=
    eq_of_heq (finiteSingleComparison_heq A X)
  unfold coefficientUnitIso finiteUnitComparison
  rw [he]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.compIsoApp]
  rw [constant_comparison_unit]
  simp only [Category.assoc]
  rfl

private theorem native_single_unit
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Functor.compIsoApp
        (singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} A) f)
        (geoCartierConstant A Y)).hom ≫
      (DerivedCategory.singleFunctor _ 0).map
        (Functor.OplaxMonoidal.η (upperStar (ModuleCat.{u + 1} A) f)) ≫
      (DerivedCategory.singleFunctorObjUnitIso
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))).hom =
    (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.map
        (DerivedCategory.singleFunctorObjUnitIso
          (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A))).hom ≫
      (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) f).hom := by
  have hε (Z : Scheme.{u}) : Functor.LaxMonoidal.ε
      (DerivedCategory.Qh (C := Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A))) =
        𝟙 _ := rfl
  have hq (Z : Scheme.{u}) (K : CochainComplex
      (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A)) ℤ) :
      (DerivedCategory.quotientCompQhIso _).inv.app K = 𝟙 _ := rfl
  have hηq (Z : Scheme.{u}) : (Functor.Monoidal.εIso (HomotopyCategory.quotient
      (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A)) (.up ℤ))).inv = 𝟙 _ := rfl
  unfold leftDerivedUpperStarUnitIso
  simp only [Iso.trans_hom, Iso.app_hom]
  unfold Functor.compIsoApp singleFunctorCompLeftDerivedUpperStarIso
    Functor.singleFunctorCompLeftDerivedFunctorIso
  simp only [Iso.app_hom, Iso.trans_hom, Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.comp_obj]
  rw [(leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).hom.naturality_assoc]
  erw [Category.assoc, cancel_epi]
  unfold DerivedCategory.singleFunctorObjUnitIso
  dsimp only [Functor.mapDerivedCategorySingleFunctor, DerivedCategory.singleFunctorIsoCompQ,
    Functor.isoWhiskerLeft, Functor.isoWhiskerRight, Functor.associator,
    Functor.whiskeringLeft, Functor.whiskeringRight, Functor.mapIso, Iso.app, Iso.refl,
    Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Functor.mapIso_hom, Iso.refl_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.id_app]
  simp only [hε, hq, hηq, asIso_inv, IsIso.inv_id, CategoryTheory.Functor.map_id,
    Category.id_comp, Functor.map_comp, Category.assoc]
  try dsimp only [Functor.whiskerRight, Functor.whiskerLeft, NatTrans.id_app]
  repeat first
    | erw [CategoryTheory.Functor.map_id]
    | erw [Category.id_comp]
    | erw [Category.comp_id]
  rfl


/-- The compared ordinary coefficient unit pulls back by the native derived unit map.
Source: canonical constant-coefficient pullback in the affine tensor coordinates
(blueprint: lem-pur-compared-pullback-unit).
Proof: the constant-sheaf comparison is the monoidal unit by uniqueness of the
constant-object adjunction. Thus finiteUnitComparison followed by the degree-zero
unit is coefficientUnitIso. Apply finite_constant_pullback_comparison, and use
naturality of the exact-derived single comparison. Its value on the unit is the
native unit isomorphism by its defining complex-level formula. -/
theorem compared_pullback_unit (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pullbackUnit A f).hom ≫ (coefficientUnitIso (ModuleCat.{u + 1} A) X).hom =
      (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.map
        (coefficientUnitIso (ModuleCat.{u + 1} A) Y).hom ≫
      (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) f).hom := by
  rw [coefficient_finite_unit, coefficient_finite_unit, Functor.map_comp]
  rw [← Category.assoc, show (pullbackUnit A f).hom = (geoP1UnitPullback A f).hom by
      unfold pullbackUnit; rfl,
    finite_constant_pullback_comparison]
  simp only [Category.assoc]
  rw [native_single_unit]
  rfl

end AlgebraicGeometry.ProEtale.OrderedProjectionUnit
end
