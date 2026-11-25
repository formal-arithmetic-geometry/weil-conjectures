/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerP1.TowerP1CoefficientCoordinates
public import WeilConjectures.AlgebraicGeometry.Geo.GeoP1Cohomology

/-! # Finite coefficient coordinate definitions
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
open SpTowerClasses

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The inverse of the constant-section-normalized coefficient word. -/
def finiteUnitCoordinate (n : ℕ) [Finite (SpTowerShriek.R l E n)]
    (T : Scheme.{u}) {hT : IsUnit ((l ^ (n + 1) : ℕ) : Γ(T, ⊤))}
    (c : SpTowerP1.CoefficientCoordinates l E n T hT) :
    (SpTowerShriek.Ev l E T n).obj (unit T (Arings l E T)) ≅
      (Scheme.sfIntrinsicModuleEquivalence T (SpTowerShriek.R l E n)).functor.mapDerivedCategory.obj
        (geoP1Unit (FiniteRing l E n) T) :=
  (SpTowerP1.nuSingle l E n T _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso c.unit ≪≫
    (((SpTowerShriek.ev l E T n).mapDerivedCategorySingleFunctor 0).app _).symm).symm

/-- Realize a fixed-scalar object on P¹ on an isomorphic scheme X. -/
abbrev finiteOverRealization (n : ℕ) [Finite (SpTowerShriek.R l E n)]
    {X S : Scheme.{u}} (e : X ≅ ProjectiveLine S) :=
  geoP1Pullback (FiniteRing l E n) e.hom ⋙
    (Scheme.sfIntrinsicModuleEquivalence X (SpTowerShriek.R l E n)).functor.mapDerivedCategory

/-- The normalized source comparison, including pullback along e. -/
def finiteOverUnitCoordinate (n : ℕ) [Finite (SpTowerShriek.R l E n)]
    {X S : Scheme.{u}} (e : X ≅ ProjectiveLine S)
    {hX : IsUnit ((l ^ (n + 1) : ℕ) : Γ(X, ⊤))}
    (c : SpTowerP1.CoefficientCoordinates l E n X hX) :
    (SpTowerShriek.Ev l E X n).obj (unit X (Arings l E X)) ≅
      (finiteOverRealization l E n e).obj (geoP1Unit (FiniteRing l E n) (ProjectiveLine S)) :=
  finiteUnitCoordinate l E n X c ≪≫
    (Functor.mapDerivedCategory
      (Scheme.sfIntrinsicModuleEquivalence X (SpTowerShriek.R l E n)).functor).mapIso
      (geoP1UnitPullback (FiniteRing l E n) e.hom).symm

end AlgebraicGeometry.ProEtale.DiagonalTrace
