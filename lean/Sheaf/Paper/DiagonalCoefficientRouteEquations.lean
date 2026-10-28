/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E2
-/
module

public import Sheaf.Paper.DiagonalCoefficientRouteComparison

/-! # Endpoint equations for the finite coefficient comparison

Source: diagonal tower coefficient changes (1), derived adjunction transitivity.
(blueprint: def-diagonal-coefficient-route-equations).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

-- Use the module-sheaf abelian structure of GeoCartierClass.
attribute [local instance 100000] sheafIsAbelian
attribute [local instance 200000] AlgebraicGeometry.ProEtale.diagonalAbSheafAbelian
attribute [local instance 300000] CommRing.toRing
attribute [local instance 400000] AlgebraicGeometry.ProEtale.diagonalModuleSheafAbelian
namespace UniformizerSquareData

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}}
  {E : PadicAlgCl.FiniteIntermediateField l} {π : PadicAlgCl.integers l E} {n : ℕ}
  {A : Type (u + 1)} [CommRing A] {hA : ((l ^ (n + 1) : ℕ) : A) = 0}
  (q : UniformizerSquareData l Y E π n A hA)

attribute [local irreducible] derivedScalars quotientLine quotientLineMap cyclicLine cyclicLineMap
  Functor.leftDerivedFunctor Mod.derivedExtendMapDerivedCategoryAdjunction
  HasDerivedCategory.standard DerivedCategory.singleFunctors
  HomotopyCategory.singleFunctors DerivedCategory.singleFunctorIsoCompQ

/-- The supported constant endpoint equation, without any diagonal-class equation. -/
def SourceEquation (s : q.quotientRight ≅ q.restriction ⋙ q.cyclicRight) : Prop :=
  (q.comparison s).app q.initialSource ≫
      q.restriction.mapDerivedCategory.map q.quotientSource.hom ≫
        (q.restriction.mapDerivedCategorySingleFunctor 0).hom.app _ =
    q.cyclicSource.hom ≫ (DerivedCategory.singleFunctor _ 0).map q.sourceMap

/-- The positive root endpoint equation, without any diagonal-class equation. -/
def TargetEquation (s : q.quotientRight ≅ q.restriction ⋙ q.cyclicRight) : Prop :=
  (q.comparison s).app q.initialTarget ≫
      q.restriction.mapDerivedCategory.map q.quotientTarget ≫
        (q.restriction.mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app _ ≫
          ((q.restriction.mapDerivedCategorySingleFunctor 0).hom.app _)⟦(2 : ℤ)⟧' =
    q.cyclicTarget ≫ ((DerivedCategory.singleFunctor _ 0).map q.lineMap)⟦(2 : ℤ)⟧'

end UniformizerSquareData
end AlgebraicGeometry.ProEtale.DiagonalCoefficients
