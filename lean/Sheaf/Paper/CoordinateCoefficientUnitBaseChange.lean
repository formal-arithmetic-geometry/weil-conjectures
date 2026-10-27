/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E8
-/
module

public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Arrows
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
import Sheaf.Paper.CoordinateSingleConstantPullbackComparison

/-! # Compatibility of constant-coefficient pullback with the derived unit -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

set_option linter.auxLemma false in
attribute [local instance 100000]
  ordinaryFinitePullback._proof_1 ordinaryFinitePullback._proof_2
  ordinaryFinitePullback._proof_3 ordinaryFinitePullback._proof_4
  ordinaryFinitePullback._proof_5 ordinaryFinitePullback._proof_6
  ordinaryFinitePullback._proof_7 ordinaryFinitePullback._proof_8
  ordinaryFinitePullback._proof_9 ordinaryFinitePullback._proof_10
  ordinaryFinitePullback._proof_11 ordinaryFinitePullback._proof_12
  ordinaryFinitePullback._proof_13

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  HasDerivedCategory.ofIsGrothendieckAbelian DerivedCategory.singleFunctors
  leftDerivedUpperStarIsoMapDerivedCategory

private theorem unit_cancel
    {C D : Type*} [Category C] [Category D] (P : C ⥤ D)
    {U I : C} {U' I' : D} (u : U ≅ I) (u' : U' ≅ I')
    (j : P.obj U ⟶ U') (r : P.obj I ⟶ I')
    (h : P.map u.inv ≫ j = r ≫ u'.inv) :
    j ≫ u'.hom = P.map u.hom ≫ r := by
  apply (cancel_epi (P.map u.inv)).mp
  simp only [← P.map_comp_assoc, Iso.inv_hom_id, P.map_id, Category.id_comp]
  rw [← Category.assoc, h]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The ordinary constant-coefficient pullback comparison agrees with derived units.
Source: sk-thm-dnc, Local construction, canonical constant-coefficient identifications
(blueprint: lem-trf-coordinate-coefficient-unit-base-change).

Proof: Expanding the ordinary constant pullback comparison and using the recorded
single/exact-pullback comparison identifies it with the derived single-constant-sheaf
comparison. The inverse form of unit compatibility is
P.map(u.inv) followed by that comparison equals the derived-unit pullback followed by
u'.inv. Precompose the desired identity by P.map(u.inv), use this equality, and cancel
the two unit isomorphisms. No invertibility or nonzero condition on coefficients is used.
-/
theorem coordinateCoefficientUnit_baseChange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S T : Scheme.{u}} (v : T ⟶ S) :
    (ordinaryFiniteUnitPullback A v).hom ≫
        (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) T).hom =
      (ordinaryFinitePullback A v).map
          (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) S).hom ≫
        (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) v).hom := by
  apply unit_cancel
  rw [coordinateUnitPullback_eq_singleConstant]
  exact leftDerivedUpperStar_map_singleFunctorObjUnitIso_inv_comp
    (ModuleCat.{u + 1} A) v

end AlgebraicGeometry.Etale
