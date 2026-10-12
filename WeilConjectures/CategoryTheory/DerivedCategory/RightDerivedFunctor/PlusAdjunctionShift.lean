/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryAdjunctionShift
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Plus
public import WeilConjectures.Mathlib.CategoryTheory.Shift.CommShift

/-!
# The bounded below derived adjunction commutes with the shifts

Let `L ⊣ R` be an adjunction of additive functors between abelian categories, with `L` exact
and the target of `L` having enough injectives. The bounded below derived adjunction
`L.mapDerivedCategoryPlus ⊣ R.rightDerivedFunctorPlus`
(`CategoryTheory.Adjunction.derivedPlus`) is compatible with the shift structures of the two
functors (`CategoryTheory.Adjunction.commShift_derivedPlus`): the shift structure of
`L.mapDerivedCategoryPlus` is induced by `L` termwise, and that of `R.rightDerivedFunctorPlus`
is transported from complexes of injectives, i.e. obtained by comparing injective resolutions.

The proof reduces to the unit (`CategoryTheory.Adjunction.CommShift.mk'`). Mathlib also gives
the compatibility of the counit
(`CategoryTheory.Adjunction.CommShift.compatibilityCounit_of_compatibilityUnit`) and the
uniqueness of the shift structure on the right adjoint
(`CategoryTheory.Adjunction.rightAdjointCommShift`); this is blueprint
`lem-weil-pbc-adjunction-shift-compatibility-unique`. On the image of a bounded below complex
`K`, the derived unit is the unit of `L ⊣ R` on `K` followed by the unit of the right derived
functor of `R` at `L(K)` (`CategoryTheory.Adjunction.derivedPlus_unit_app_fac`), and both commute
with the shifts.

This is blueprint `lem-weil-pbc-derived-adjunction-commshift`
(`CategoryTheory.Adjunction.derivedPlus_unit_app_shift`,
`CategoryTheory.Adjunction.derivedPlus_counit_app_shift`).
-/

@[expose] public section

open CategoryTheory Category Limits

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive] (adj : L ⊣ R)

/-- The unit of the adjunction `L.mapHomotopyCategoryPlus ⊣ R.mapHomotopyCategoryPlus`
commutes with the shifts. -/
instance commShift_mapHomotopyCategoryPlus_unit :
    NatTrans.CommShift adj.mapHomotopyCategoryPlus.unit ℤ := by
  have : Functor.whiskerRight adj.mapHomotopyCategoryPlus.unit (HomotopyCategory.Plus.ι C) =
      (Functor.leftUnitor _).hom ≫ (Functor.rightUnitor _).inv ≫
        Functor.whiskerLeft (HomotopyCategory.Plus.ι C) (adj.mapHomotopyCategory (.up ℤ)).unit ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight ((HomotopyCategory.plus D).liftCompιIso _ _ :
            L.mapHomotopyCategoryPlus ⋙ HomotopyCategory.Plus.ι D ≅ _).inv
          (R.mapHomotopyCategory (.up ℤ)) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft L.mapHomotopyCategoryPlus
          ((HomotopyCategory.plus C).liftCompιIso _ _ :
            R.mapHomotopyCategoryPlus ⋙ HomotopyCategory.Plus.ι C ≅ _).inv ≫
        (Functor.associator _ _ _).inv := by
    ext K
    simp [ObjectProperty.liftCompιIso]
    exact (adj.ι_map_mapHomotopyCategoryPlus_unit_app K).trans (comp_id _).symm
  have : NatTrans.CommShift (Functor.whiskerRight adj.mapHomotopyCategoryPlus.unit
      (HomotopyCategory.Plus.ι C)) ℤ := by
    rw [this]
    infer_instance
  exact NatTrans.CommShift.of_whiskerRight _ (HomotopyCategory.Plus.ι C)

variable [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives D]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]

/-- The unit of the bounded below derived adjunction commutes with the shifts. -/
instance commShift_derivedPlus_unit : NatTrans.CommShift adj.derivedPlus.unit ℤ := by
  let Qh := DerivedCategory.Plus.Qh (C := C)
  let θ : Qh ⋙ L.mapDerivedCategoryPlus ⋙ R.rightDerivedFunctorPlus ⟶
      L.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⋙ R.rightDerivedFunctorPlus :=
    (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight L.mapDerivedCategoryPlusFactorsh.hom R.rightDerivedFunctorPlus ≫
      (Functor.associator _ _ _).hom
  have hθ : NatTrans.CommShift θ ℤ := by dsimp only [θ]; infer_instance
  have : IsIso θ := by dsimp only [θ]; infer_instance
  have h : Functor.whiskerLeft Qh adj.derivedPlus.unit ≫ θ =
      (Functor.rightUnitor Qh).hom ≫ (Functor.leftUnitor Qh).inv ≫
        Functor.whiskerRight adj.mapHomotopyCategoryPlus.unit DerivedCategory.Plus.Qh ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft L.mapHomotopyCategoryPlus R.rightDerivedFunctorPlusUnit := by
    refine NatTrans.ext (funext fun K ↦ ?_)
    simpa [θ] using adj.derivedPlus_unit_app_fac K
  have : NatTrans.CommShift (Functor.whiskerLeft Qh adj.derivedPlus.unit) ℤ := by
    have : NatTrans.CommShift (inv θ) ℤ := NatTrans.CommShift.of_isIso _ _
    rw [← IsIso.eq_comp_inv] at h
    rw [h]
    infer_instance
  exact NatTrans.CommShift.of_whiskerLeft _ DerivedCategory.Plus.Qh
    (fun X ↦ ⟨_, (DerivedCategory.Plus.Qh.objObjPreimageIso X).inv, inferInstance⟩)

/-- The bounded below derived adjunction `L.mapDerivedCategoryPlus ⊣ R.rightDerivedFunctorPlus`
is compatible with the shifts (blueprint `lem-weil-pbc-derived-adjunction-commshift`). -/
instance commShift_derivedPlus : adj.derivedPlus.CommShift ℤ :=
  Adjunction.CommShift.mk' _ _ (adj.commShift_derivedPlus_unit)

/-- This is blueprint `lem-weil-pbc-derived-adjunction-commshift` (b): the unit
`η : M ⟶ R⁺(L⁺ M)` of the bounded below derived adjunction commutes with the shift isomorphism
of the composite functor `L⁺ ⋙ R⁺` (which is the composite of the shift isomorphisms of `R⁺`
and `L⁺`, `CategoryTheory.Functor.commShiftIso_comp_hom_app`). -/
@[reassoc]
lemma derivedPlus_unit_app_shift (M : DerivedCategory.Plus C) (n : ℤ) :
    adj.derivedPlus.unit.app (M⟦n⟧) ≫
        ((L.mapDerivedCategoryPlus ⋙ R.rightDerivedFunctorPlus).commShiftIso n).hom.app M =
      (adj.derivedPlus.unit.app M)⟦n⟧' := by
  simp

/-- This is blueprint `lem-weil-pbc-derived-adjunction-commshift` (a): the counit
`ε : L⁺(R⁺ K) ⟶ K` of the bounded below derived adjunction commutes with the shift isomorphism
of the composite functor `R⁺ ⋙ L⁺`. -/
@[reassoc]
lemma derivedPlus_counit_app_shift (K : DerivedCategory.Plus D) (n : ℤ) :
    ((R.rightDerivedFunctorPlus ⋙ L.mapDerivedCategoryPlus).commShiftIso n).hom.app K ≫
        (adj.derivedPlus.counit.app K)⟦n⟧' =
      adj.derivedPlus.counit.app (K⟦n⟧) := by
  simp

end CategoryTheory.Adjunction
