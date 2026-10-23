/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.AdjunctionShift
public import WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction

/-!
# The canonical shift structure of a right derived functor and the derived adjunction

Let `F : C ⥤ D` be an additive functor between abelian categories, `C` with K-injective
resolutions. The right derived functor `F.rightDerivedFunctor` carries the shift structure
transported from the termwise functor on K-injective complexes
(`CategoryTheory.Functor.rightDerivedFunctor`, instance in
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated`).

* `CategoryTheory.Functor.commShift_rightDerivedFunctorUnit`: for this structure, the unit
  `F.mapHomotopyCategory ⋙ Qh ⟶ Qh ⋙ F.rightDerivedFunctor` commutes with the shifts.
* `CategoryTheory.Functor.commShift_eq_of_isLeftKanExtension`: a left Kan extension carries at
  most one shift structure for which its unit commutes with the shifts.
* `CategoryTheory.Adjunction.commShift_mapDerivedCategoryRightDerivedAdjunction`: for an
  adjunction `L ⊣ R` with `L` exact, the derived adjunction
  `L.mapDerivedCategory ⊣ R.rightDerivedFunctor` commutes with the shifts, for the canonical
  shift structure of `R.rightDerivedFunctor`. Indeed, the structure transported from
  `L.mapDerivedCategory` along the adjunction also makes the unit commute with the shifts
  (`CategoryTheory.Adjunction.commShift_rightDerivedFunctorUnit`), so the two structures agree.
-/

@[expose] public section

open CategoryTheory Category Limits Abelian

namespace CategoryTheory

namespace Functor

section Unit

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasKInjectiveResolutions C]
  (F : C ⥤ D) [F.Additive]

set_option backward.isDefEq.respectTransparency false in
/-- The unit `F.mapHomotopyCategory ⋙ Qh ⟶ Qh ⋙ F.rightDerivedFunctor` commutes with the shifts,
for the shift structure of `F.rightDerivedFunctor` transported from K-injective complexes: on
K-injective complexes it is the transport isomorphism up to the unit of the equivalence
`K(Inj) ≌ D(C)`, and every complex is isomorphic in `D(C)` to a K-injective one. -/
instance commShift_rightDerivedFunctorUnit :
    NatTrans.CommShift F.rightDerivedFunctorUnit ℤ := by
  let inj := ObjectProperty.ι (HomotopyCategory.subcategoryAcyclic C).rightOrthogonal
  let E := HomotopyCategory.KInjectives.equivalence C
  let G := inj ⋙ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  have : NatTrans.CommShift F.rightDerivedFunctorIsoKInjectives.inv ℤ :=
    Functor.CommShift.ofIso_compatibility F.rightDerivedFunctorIsoKInjectives.symm ℤ
  have hinv (Y : DerivedCategory C) :
      F.rightDerivedFunctorIsoKInjectives.inv.app Y =
        F.rightDerivedFunctorUnit.app (inj.obj (E.inverse.obj Y)) ≫
          F.rightDerivedFunctor.map (E.counit.app Y) := by
    simp [Functor.rightDerivedFunctorIsoKInjectives, inj, E]
  have heq : whiskerLeft inj F.rightDerivedFunctorUnit =
      (leftUnitor G).inv ≫ whiskerRight E.unitIso.hom G ≫
        (associator E.functor E.inverse G).hom ≫
        whiskerLeft E.functor F.rightDerivedFunctorIsoKInjectives.inv ≫
        (associator inj DerivedCategory.Qh F.rightDerivedFunctor).hom := by
    ext X
    simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
      associator_hom_app, leftUnitor_inv_app, Category.id_comp, hinv]
    simp only [Category.assoc]
    erw [Category.id_comp, Category.comp_id]
    have h := F.rightDerivedFunctorUnit.naturality (inj.map (E.unit.app X))
    dsimp only [Functor.comp_map, Functor.comp_obj] at h
    change _ = (F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh).map
      (inj.map (E.unit.app X)) ≫ _
    erw [reassoc_of% h]
    rw [← CategoryTheory.Functor.map_comp]
    change _ = _ ≫ F.rightDerivedFunctor.map
      (E.functor.map (E.unit.app X) ≫ E.counit.app (E.functor.obj X))
    erw [E.functor_unit_comp]
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
  have : NatTrans.CommShift (whiskerLeft inj F.rightDerivedFunctorUnit) ℤ := by
    rw [heq]
    infer_instance
  refine NatTrans.CommShift.of_whiskerLeft _ inj (fun K ↦ ?_)
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  obtain ⟨I, hI, i, hi, _⟩ := HasKInjectiveResolutions.exists_isKInjective P
  refine ⟨HomotopyCategory.KInjectives.mk I, (HomotopyCategory.quotient C (.up ℤ)).map i, ?_⟩
  change IsIso (F.rightDerivedFunctor.map (DerivedCategory.Q.map i))
  infer_instance

end Unit

section KanExtension

variable {C D E : Type*} [Category C] [Category D] [Category E]
  [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ]

set_option backward.isDefEq.respectTransparency false in
/-- A left Kan extension `LF` of `F` along `Q` carries at most one shift structure for which the
unit `α : F ⟶ Q ⋙ LF` commutes with the shifts: postcomposition with the shift functor, an
equivalence, preserves left Kan extensions, and the inverses of the two commutation
isomorphisms agree after whiskering with `α`. -/
lemma commShift_eq_of_isLeftKanExtension (Q : C ⥤ D) (F : C ⥤ E) [Q.CommShift ℤ]
    [F.CommShift ℤ] (LF : D ⥤ E) (α : F ⟶ Q ⋙ LF) [LF.IsLeftKanExtension α]
    (s t : LF.CommShift ℤ) (hs : letI := s; NatTrans.CommShift α ℤ)
    (ht : letI := t; NatTrans.CommShift α ℤ) : s = t := by
  have hiso (n : ℤ) : s.commShiftIso n = t.commShiftIso n := by
    let γ := whiskerRight α (shiftFunctor E n) ≫ (associator Q LF (shiftFunctor E n)).hom
    let P := LeftExtension.postcompose₂ Q F (shiftFunctor E n)
    have : P.IsEquivalence := by
      dsimp only [P, LeftExtension.postcompose₂]
      let δ : (whiskeringLeft C D E).obj Q ⋙
          ((whiskeringRight C E E).obj (shiftFunctor E n)) ⟶
          ((whiskeringRight D E E).obj (shiftFunctor E n)) ⋙
            (whiskeringLeft C D E).obj Q :=
        { app H := (associator Q H (shiftFunctor E n)).hom }
      have : IsIso δ := by apply NatIso.isIso_of_isIso_app
      exact StructuredArrow.isEquivalenceMap₂ (𝟙 _) δ
    have : (LF ⋙ shiftFunctor E n).IsLeftKanExtension γ := by
      constructor
      refine ⟨Limits.IsInitial.ofIso
        (Limits.IsInitial.isInitialObj P _ (LF.isUniversalOfIsLeftKanExtension α)) ?_⟩
      exact LeftExtension.postcompose₂ObjMkIso (shiftFunctor E n) α
    have hshift (v : LF.CommShift ℤ) (hv : letI := v; NatTrans.CommShift α ℤ) (M : C) :
        (α.app M)⟦n⟧' ≫ (v.commShiftIso n).inv.app (Q.obj M) =
          (F.commShiftIso n).inv.app M ≫ α.app (M⟦n⟧) ≫
            LF.map ((Q.commShiftIso n).hom.app M) := by
      let := v
      have h := NatTrans.shift_app_comm α n M
      rw [Functor.commShiftIso_comp_hom_app] at h
      rw [← cancel_epi ((F.commShiftIso n).hom.app M), reassoc_of% h, Iso.hom_inv_id_app_assoc]
      simp only [Iso.hom_inv_id_app]
      erw [Category.comp_id]
    have e : (s.commShiftIso n).inv = (t.commShiftIso n).inv :=
      (LF ⋙ shiftFunctor E n).hom_ext_of_isLeftKanExtension γ _ _ (by
        ext M
        dsimp only [γ, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
          associator_hom_app]
        simp only [Category.comp_id]
        exact (hshift s hs M).trans (hshift t ht M).symm)
    exact Iso.ext ((Iso.inv_eq_inv _ _).1 e)
  cases s
  cases t
  congr 1
  funext n
  exact hiso n

end KanExtension

end Functor

namespace Adjunction

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive] (adj : L ⊣ R)
  [HasDerivedCategory C] [HasDerivedCategory D] [HasKInjectiveResolutions D]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]

/-- The derived adjunction `L.mapDerivedCategory ⊣ R.rightDerivedFunctor` of an adjunction
with exact left adjoint commutes with the shifts, for the canonical shift structure of the right
derived functor: the structure transported along the adjunction makes the unit of the right
derived functor commute with the shifts, hence agrees with the canonical one
(`Functor.commShift_eq_of_isLeftKanExtension`). -/
instance commShift_mapDerivedCategoryRightDerivedAdjunction :
    adj.mapDerivedCategoryRightDerivedAdjunction.CommShift ℤ := by
  let t := adj.mapDerivedCategoryRightDerivedAdjunction.rightAdjointCommShift ℤ
  have h₁ : letI := t; adj.mapDerivedCategoryRightDerivedAdjunction.CommShift ℤ :=
    adj.mapDerivedCategoryRightDerivedAdjunction.commShift_of_leftAdjoint ℤ
  have ht : letI := t; NatTrans.CommShift R.rightDerivedFunctorUnit ℤ := by
    let := t
    exact adj.commShift_rightDerivedFunctorUnit
  clear_value t
  have : R.rightDerivedFunctor.IsLeftKanExtension R.rightDerivedFunctorUnit :=
    (Functor.isRightDerivedFunctor_iff_isLeftKanExtension _ _
      (HomotopyCategory.quasiIso D (ComplexShape.up ℤ))).1 inferInstance
  have heq : R.instCommShiftDerivedCategoryRightDerivedFunctorInt = t :=
    Functor.commShift_eq_of_isLeftKanExtension DerivedCategory.Qh _ R.rightDerivedFunctor
      R.rightDerivedFunctorUnit _ t (R.commShift_rightDerivedFunctorUnit) ht
  have key : ∀ s : R.rightDerivedFunctor.CommShift ℤ, s = t →
      letI := s; adj.mapDerivedCategoryRightDerivedAdjunction.CommShift ℤ := by
    rintro s rfl
    exact h₁
  exact key _ heq

end Adjunction

end CategoryTheory
