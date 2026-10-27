/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.AlgebraicGeometry.GeoP1Cohomology
public import Sheaf.AlgebraicGeometry.OrdinarySupportedKummerSystem

/-!
# Exact derived realization of Cartier classes

Source: blueprint main-20261015, det-sp-p1-trace, clause 3: the canonical
identification of the Ext cycle class with its derived closed-image arrow
(blueprint: def-sp-cartier-derived-realization).

The predicate uses the existing exact-direct-image realization, with specified
source and target isomorphisms. It applies to any exact additive functor.
The named constant and shifted-line comparisons supply its ordinary pro-etale
specialization without choosing an identification.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

universe u uC vC wC uD vD wD

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- Identify the derived arrow with this very Ext class through exact direct image.
The two isomorphisms only transport the fixed degree-zero source and shifted target.
Source: det-sp-p1-trace, clause 3 (blueprint: def-sp-cartier-derived-realization). -/
@[irreducible]
def CartierDerivedCompatibility {C : Type uC} [Category.{vC} C] [Abelian C]
    [HasDerivedCategory.{wC} C] [HasKInjectiveResolutions C]
    {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]
    [HasExt.{wD} D] (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    [hF : PreservesFiniteColimits F] (X : C) (Y : D)
    {Z : DerivedCategory C} {W : DerivedCategory D}
    (s : Z ≅ (DerivedCategory.singleFunctor C 0).obj X)
    (t : W ≅ ((DerivedCategory.singleFunctor D 0).obj Y)⟦(2 : ℤ)⟧)
    (c : Ext (F.obj X) Y 2) {δType : Type wD} (δ : δType) : Prop :=
  HEq δ (F.rightDerivedFunctor.map s.hom ≫
    Etale.supportedExactDerivedMap F X Y c ≫ t.inv)

/-- The canonical identification of the comparison-defined constant with degree zero.
Source: det-sp-p1-trace, clause 3 (blueprint: def-sp-cartier-derived-realization). -/
@[irreducible]
def cartierUnitSingleIso (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    geoP1Unit A T ≅ (DerivedCategory.singleFunctor _ 0).obj (geoCartierConstant A T) :=
  ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategorySingleFunctor 0).app
      (Etale.ordinaryFiniteConstant A T) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      ((comparisonUpperStarConstantSheafIso A T).app (ModuleCat.of A A))

/-- The canonical shift and degree-zero comparison for the positive Tate line.
Source: det-sp-p1-trace, clause 3 (blueprint: def-sp-cartier-derived-realization). -/
@[irreducible]
def cartierShiftSingleIso {C : Type uC} [Category.{vC} C] [Abelian C]
    [HasDerivedCategory.{wC} C] {D : Type uD} [Category.{vD} D] [Abelian D]
    [HasDerivedCategory.{wD} D] (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (Y : C) :
    F.mapDerivedCategory.obj (((DerivedCategory.singleFunctor C 0).obj Y)⟦(2 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor D 0).obj (F.obj Y))⟦(2 : ℤ)⟧ :=
  (F.mapDerivedCategory.commShiftIso (2 : ℤ)).app
      ((DerivedCategory.singleFunctor C 0).obj Y) ≪≫
    (shiftFunctor _ (2 : ℤ)).mapIso ((F.mapDerivedCategorySingleFunctor 0).app Y)

end AlgebraicGeometry.ProEtale
