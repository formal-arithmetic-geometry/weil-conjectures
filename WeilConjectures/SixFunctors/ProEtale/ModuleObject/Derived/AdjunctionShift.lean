/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.UnitShift
public import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarShift

/-!
# The derived adjunctions on module objects commute with the shifts

The derived pullback `L((f)^*⟦Λ⟧)` on module objects carries the shift structure transported
from the levelwise functor `D((f)^*⟦Λ⟧)`
(`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarShift`), and the derived
pushforward `R((f)_*⟦Λ⟧)` the one of right derived functors. This file shows:

* the derived adjunction `Lf^* ⊣ Rf_*` commutes with the shifts
  (`ProEtale.CondensedRing.commShift_derivedUpperStarLowerStarAdjunction`);
* for an open immersion `j`, the adjunction `j_! ⊣ Lj^*` commutes with the shifts
  (`ProEtale.CondensedRing.commShift_derivedOpenImmersionLowerShriekUpperStarAdjunction`);
* the composition isomorphism `L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*` commutes with the shifts
  (`ProEtale.CondensedRing.commShift_leftDerivedUpperStarComp_hom`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The identification `L((f)^*⟦Λ⟧) ≅ D((f)^*⟦Λ⟧)` commutes with the shifts. -/
instance commShift_leftDerivedUpperStarIsoMapDerivedCategory_hom {X Y : Scheme.{u}}
    (f : X ⟶ Y) : NatTrans.CommShift (leftDerivedUpperStarIsoMapDerivedCategory Λ f).hom ℤ :=
  NatTrans.CommShift.of_iso_inv (leftDerivedUpperStarIsoMapDerivedCategory Λ f).symm ℤ

/-- The inverse of the identification `L((f)^*⟦Λ⟧) ≅ D((f)^*⟦Λ⟧)` commutes with the shifts. -/
instance commShift_leftDerivedUpperStarIsoMapDerivedCategory_inv {X Y : Scheme.{u}}
    (f : X ⟶ Y) : NatTrans.CommShift (leftDerivedUpperStarIsoMapDerivedCategory Λ f).inv ℤ :=
  inferInstanceAs (NatTrans.CommShift (leftDerivedUpperStarIsoMapDerivedCategory Λ f).symm.hom ℤ)

/-- The derived adjunction `Lf^* ⊣ Rf_*` is the adjunction `D(f^*) ⊣ Rf_*` transported along
`Lf^* ≅ D(f^*)`. -/
lemma derivedUpperStarLowerStarAdjunction_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    derivedUpperStarLowerStarAdjunction Λ f =
      (upperStarLowerStarAdjunction Λ f).mapDerivedCategoryRightDerivedAdjunction.ofNatIsoLeft
        (leftDerivedUpperStarIsoMapDerivedCategory Λ f).symm :=
  Adjunction.derived_eq_ofNatIsoLeft _ _ _ _ _ _
    (leftDerivedUpperStarIsoMapDerivedCategory Λ f)
    ((f)^*⟦Λ⟧.leftDerivedFunctorIsoMapDerivedCategory_hom_fac).symm

/-- The derived adjunction `Lf^* ⊣ Rf_*` on module objects commutes with the shifts. -/
instance commShift_derivedUpperStarLowerStarAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (derivedUpperStarLowerStarAdjunction Λ f).CommShift ℤ := by
  rw [derivedUpperStarLowerStarAdjunction_eq]
  exact Adjunction.commShift_ofNatIsoLeft _ _

/-- The adjunction `j_! ⊣ Lj^*` along an open immersion, transported from the levelwise
adjunction `D(j_!) ⊣ D(j^*)`, commutes with the shifts. -/
instance commShift_derivedOpenImmersionLowerShriekUpperStarAdjunction {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] :
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).ofNatIsoRight
      (leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion Λ j).symm).CommShift ℤ :=
  haveI : NatTrans.CommShift
      (leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion Λ j).symm.hom ℤ :=
    inferInstanceAs (NatTrans.CommShift (leftDerivedUpperStarIsoMapDerivedCategory Λ j).inv ℤ)
  haveI : (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).CommShift ℤ :=
    inferInstanceAs
      ((openImmersionLowerShriekUpperStarAdjunction Λ j).mapDerivedCategoryAdjunction.CommShift ℤ)
  Adjunction.commShift_ofNatIsoRight _ _

/-- The composition isomorphism `L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*` commutes with the shifts. -/
instance commShift_leftDerivedUpperStarComp_hom {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) : NatTrans.CommShift (leftDerivedUpperStarComp Λ f g).hom ℤ := by
  have e : (leftDerivedUpperStarComp Λ f g).hom =
      (leftDerivedUpperStarIsoMapDerivedCategory Λ (f ≫ g)).hom ≫
        (Functor.mapDerivedCategoryNatIso (upperStarComp Λ f g)).hom ≫
        ((g)^*⟦Λ⟧.mapDerivedCategoryCompIso (f)^*⟦Λ⟧).hom ≫
        Functor.whiskerRight (leftDerivedUpperStarIsoMapDerivedCategory Λ g).inv
          D((f)^*⟦Λ⟧) ≫
        Functor.whiskerLeft L((g)^*⟦Λ⟧) (leftDerivedUpperStarIsoMapDerivedCategory Λ f).inv := by
    simp [leftDerivedUpperStarComp, leftDerivedUpperStarIsoMapDerivedCategory,
      Functor.leftDerivedFunctorNatIso, Functor.leftDerivedFunctorCompIso]
  rw [e]
  infer_instance

end AlgebraicGeometry.ProEtale.CondensedRing
