/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.GeometricCoordinates.GeometricTowerIntermediate

/-! # Coordinate image of the tower compositor
Source: Stacks 0F7J; the coordinate preimage step in the compatible-tower calculation.
(blueprint: lem-sp-geometric-tower-compositors-finite-coordinate)

The proof requires expanding the fully faithful preimage and reconciling the several
independently generated derived-category instances.  This is the coordinate-level
obstacle below the finite evaluation theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerCalculus.GeometricCoordinates

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The fully faithful coordinate image of `nativeTowerCompositors` is the explicit
four-factor graph compositor followed by the inverse support coordinate.  This is
strictly below the finite evaluation statement: it contains no `Evaluation`, finite
level, or normalization argument.
Source: Stacks 0F7J, coordinate transport in Tags 0F7B--0F7K.
(blueprint: lem-sp-geometric-tower-compositors-finite-coordinate)
-/
theorem native_tower_compositors_coordinate
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : Coordinates l E b) (g : GraphCoordinates l E b o)
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {h : Y ⟶ Z}
    (T : Compactification.Triangle f h)
    (K : spDerivedCoefficientTowers l E X (q.abelian X)) :
    let := (q.abelian X).grothendieck
    let := (q.abelian X).hasDerived
    let := (q.abelian X).equivalenceAdditive
    let := (q.abelian Z).grothendieck
    let := (q.abelian Z).hasDerived
    let := (q.abelian Z).equivalenceAdditive
    let := b.realizationAdditive X
    let := b.realizationAdditive Z
    (((Functor.whiskeringRight (spDerivedCoefficientTowers l E X (q.abelian X))
      _ _).obj (nativeCoordinate l E b o q g Z).functor).map
      (((nativeCoordinate l E b o q g Z).fullyFaithfulFunctor.whiskeringRight
        (spDerivedCoefficientTowers l E X (q.abelian X))).preimage
        ((towerIntermediateCoordinates l E b o q g T).hom ≫
          Functor.whiskerLeft (nativeCoordinate l E b o q g X).functor
            (modelTowerCompositors l E T) ≫
          (nativeSupportCoordinates l E b o q g T.cfg).inv))).app K =
      (towerIntermediateCoordinates l E b o q g T).hom.app K ≫
        (modelTowerCompositors l E T).app
          ((nativeCoordinate l E b o q g X).functor.obj K) ≫
        (nativeSupportCoordinates l E b o q g T.cfg).inv.app K := by
  exact congr_app
    (((nativeCoordinate l E b o q g Z).fullyFaithfulFunctor.whiskeringRight
      (spDerivedCoefficientTowers l E X (q.abelian X))).map_preimage
      ((towerIntermediateCoordinates l E b o q g T).hom ≫
        Functor.whiskerLeft (nativeCoordinate l E b o q g X).functor
          (modelTowerCompositors l E T) ≫
        (nativeSupportCoordinates l E b o q g T.cfg).inv)) K


end AlgebraicGeometry.ProEtale.SpTowerCalculus.GeometricCoordinates
