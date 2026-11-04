/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.AdjunctionShift
public import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Shift

/-!
# The pro-étale derived base change map commutes with the shifts

For pro-étale sheaves with values in a Grothendieck abelian category `A`, the derived pullback
`Lg^*` carries the shift structure transported from `Rg_*` along the derived adjunction, while
`Rg_*` carries the shift structure transported from K-injective complexes. We show:

* `CategoryTheory.Functor.commShift_ext_of_isLeftKanExtension`: two shift structures on a left
  Kan extension for which the defining transformation commutes with the shifts agree;
* `CategoryTheory.Functor.commShift_rightDerivedFunctorUnit_kInjectives`: the unit of a total
  right derived functor commutes with the shifts for the K-injective shift structure;
* `CategoryTheory.Adjunction.commShift_mapDerivedCategoryRightDerivedAdjunction`: for `L` exact,
  the adjunction `D(L) ⊣ RR` commutes with the shifts for the K-injective structure on `RR`;
* `AlgebraicGeometry.ProEtale.commShift_leftDerivedUpperStarIsoMapDerivedCategory_hom` and
  `AlgebraicGeometry.ProEtale.commShift_derivedBaseChangeMap`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Abelian

open scoped CategoryTheory.Functor

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
open CategoryTheory.Functor in
/-- Two shift structures on a left Kan extension `LF` of `F` along `Q`, for both of which the
defining transformation `β : F ⟶ Q ⋙ LF` commutes with the shifts, agree. Shift functors are
equivalences, so they preserve the Kan universal property, which detects each comparison. -/
theorem Functor.commShift_ext_of_isLeftKanExtension
    {C D E : Type*} [Category C] [Category D] [Category E]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ]
    (Q : C ⥤ D) (F : C ⥤ E) [Q.CommShift ℤ] [F.CommShift ℤ]
    (LF : D ⥤ E) (β : F ⟶ Q ⋙ LF) [LF.IsLeftKanExtension β]
    (s t : LF.CommShift ℤ)
    (hs : letI := s; NatTrans.CommShift β ℤ)
    (ht : letI := t; NatTrans.CommShift β ℤ) : s = t := by
  have hiso (n : ℤ) : s.commShiftIso n = t.commShiftIso n := by
    let γ := whiskerRight β (shiftFunctor E n) ≫ (associator Q LF (shiftFunctor E n)).hom
    let P := LeftExtension.postcompose₂ Q F (shiftFunctor E n)
    have : P.IsEquivalence := by
      dsimp [P, LeftExtension.postcompose₂]
      let δ : (whiskeringLeft C D E).obj Q ⋙ (whiskeringRight C E E).obj (shiftFunctor E n) ⟶
          (whiskeringRight D E E).obj (shiftFunctor E n) ⋙ (whiskeringLeft C D E).obj Q :=
        { app H := (associator Q H (shiftFunctor E n)).hom }
      have : IsIso δ := by apply NatIso.isIso_of_isIso_app
      exact StructuredArrow.isEquivalenceMap₂ (𝟙 _) δ
    have : (LF ⋙ shiftFunctor E n).IsLeftKanExtension γ := by
      constructor
      refine ⟨Limits.IsInitial.ofIso
        (Limits.IsInitial.isInitialObj P _ (LF.isUniversalOfIsLeftKanExtension β)) ?_⟩
      exact LeftExtension.postcompose₂ObjMkIso (shiftFunctor E n) β
    rw [← Iso.symm_eq_iff]
    apply Iso.ext
    apply (LF ⋙ shiftFunctor E n).hom_ext_of_isLeftKanExtension γ
    ext M
    dsimp only [γ, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
      associator_hom_app, Iso.symm_hom]
    have hshift (v : LF.CommShift ℤ) (hv : letI := v; NatTrans.CommShift β ℤ) :
        (β.app M)⟦n⟧' ≫ (v.commShiftIso n).inv.app (Q.obj M) =
          (F.commShiftIso n).inv.app M ≫ β.app (M⟦n⟧) ≫
            LF.map ((Q.commShiftIso n).hom.app M) := by
      let := v
      have := hv
      have h := NatTrans.shift_app_comm β n M
      simp only [Functor.commShiftIso_comp_hom_app] at h
      rw [← cancel_epi ((F.commShiftIso n).hom.app M), Iso.hom_inv_id_app_assoc,
        ← cancel_mono ((LF.commShiftIso n).hom.app (Q.obj M))]
      simp only [Category.assoc]
      erw [Iso.inv_hom_id_app, Category.comp_id]
      rw [h]
    simpa only [Category.assoc, Category.id_comp] using (hshift s hs).trans (hshift t ht).symm
  cases s
  cases t
  congr 1
  funext n
  exact hiso n

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
open CategoryTheory.Functor CategoryTheory.Category CategoryTheory.Abelian in
/-- The unit of a total right derived functor commutes with the shifts, for the shift structure
transported from the K-injective equivalence. -/
theorem Functor.commShift_rightDerivedFunctorUnit_kInjectives
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] : NatTrans.CommShift F.rightDerivedFunctorUnit ℤ := by
  let inj := ObjectProperty.ι (HomotopyCategory.subcategoryAcyclic C).rightOrthogonal
  let E := HomotopyCategory.KInjectives.equivalence C
  let G := inj ⋙ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  have hI : NatTrans.CommShift F.rightDerivedFunctorIsoKInjectives.inv ℤ :=
    Functor.CommShift.ofIso_compatibility F.rightDerivedFunctorIsoKInjectives.symm ℤ
  have hinv (Y : DerivedCategory C) :
      F.rightDerivedFunctorIsoKInjectives.inv.app Y =
        F.rightDerivedFunctorUnit.app (inj.obj (E.inverse.obj Y)) ≫
          F.rightDerivedFunctor.map (E.counit.app Y) := by
    simp [Functor.rightDerivedFunctorIsoKInjectives, inj, E]
  have hE : E.CommShift ℤ := by infer_instance
  have hU : NatTrans.CommShift E.unitIso.hom ℤ := by infer_instance
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
  have := hI
  have := hi
  refine ⟨HomotopyCategory.KInjectives.mk I,
    (HomotopyCategory.quotient C (.up ℤ)).map i, ?_⟩
  change IsIso (F.rightDerivedFunctor.map (DerivedCategory.Q.map i))
  infer_instance

/-- For an adjunction `L ⊣ R` with `L` exact, the derived adjunction `D(L) ⊣ RR` commutes with
the shifts, where `RR` carries the shift structure transported from K-injective complexes.
Proof: the shift structure on `RR` transported from `D(L)` along the adjunction also makes the
unit of `RR` commute with the shifts, so it agrees with the K-injective one by the uniqueness of
shift structures on left Kan extensions. -/
theorem Adjunction.commShift_mapDerivedCategoryRightDerivedAdjunction
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasKInjectiveResolutions D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive] (adj : L ⊣ R)
    [PreservesFiniteLimits L] [PreservesFiniteColimits L] :
    (adj.mapDerivedCategoryRightDerivedAdjunction).CommShift ℤ := by
  let adj' := adj.mapDerivedCategoryRightDerivedAdjunction
  have hβs : NatTrans.CommShift R.rightDerivedFunctorUnit ℤ :=
    Functor.commShift_rightDerivedFunctorUnit_kInjectives R
  have ht : letI := adj'.rightAdjointCommShift ℤ; adj'.CommShift ℤ :=
    adj'.commShift_of_leftAdjoint ℤ
  have hβt : letI := adj'.rightAdjointCommShift ℤ
      NatTrans.CommShift R.rightDerivedFunctorUnit ℤ := by
    let := adj'.rightAdjointCommShift ℤ
    have := ht
    exact adj.commShift_rightDerivedFunctorUnit
  have : R.rightDerivedFunctor.IsLeftKanExtension R.rightDerivedFunctorUnit :=
    Functor.IsRightDerivedFunctor.isLeftKanExtension _ _ (HomotopyCategory.quasiIso D (.up ℤ))
  have heq : R.instCommShiftDerivedCategoryRightDerivedFunctorInt =
      adj'.rightAdjointCommShift ℤ :=
    Functor.commShift_ext_of_isLeftKanExtension DerivedCategory.Qh _ R.rightDerivedFunctor
      R.rightDerivedFunctorUnit _ _ hβs hβt
  exact heq ▸ ht

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- The derived adjunction `Lg^* ⊣ Rg_*` is the adjunction `D(g^*) ⊣ Rg_*` transported along
`Lg^* ≅ D(g^*)`. -/
lemma derivedUpperStarLowerStarAdjunction_eq_ofNatIsoLeft {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    derivedUpperStarLowerStarAdjunction A g =
      ((upperStarLowerStarAdjunction A g).mapDerivedCategoryRightDerivedAdjunction).ofNatIsoLeft
        (leftDerivedUpperStarIsoMapDerivedCategory A g).symm :=
  Adjunction.derived_eq_ofNatIsoLeft _ _ _ _ _ _
    (leftDerivedUpperStarIsoMapDerivedCategory A g)
    ((g)^*[A].leftDerivedFunctorIsoMapDerivedCategory_hom_fac).symm

/-- The identification `Lg^* ≅ D(g^*)` commutes with the shifts, for the shift structure on
`Lg^*` transported along the derived adjunction and the one on `D(g^*)` induced by the exact
functor `g^*`. -/
instance commShift_leftDerivedUpperStarIsoMapDerivedCategory_hom {Z Y : Scheme.{u}}
    (g : Z ⟶ Y) : NatTrans.CommShift (leftDerivedUpperStarIsoMapDerivedCategory A g).hom ℤ := by
  let adjM := (upperStarLowerStarAdjunction A g).mapDerivedCategoryRightDerivedAdjunction
  have : adjM.CommShift ℤ := Adjunction.commShift_mapDerivedCategoryRightDerivedAdjunction _
  have e : (leftDerivedUpperStarIsoMapDerivedCategory A g).hom =
      L((g)^*[A]).leftUnitor.inv ≫ Functor.whiskerRight adjM.unit L((g)^*[A]) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft D((g)^*[A]) (derivedUpperStarLowerStarAdjunction A g).counit ≫
        D((g)^*[A]).rightUnitor.hom := by
    ext X
    rw [derivedUpperStarLowerStarAdjunction_eq_ofNatIsoLeft]
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Adjunction.ofNatIsoLeft_counit, Iso.symm_inv]
    simp only [Functor.leftUnitor_inv_app, Functor.associator_hom_app, Functor.rightUnitor_hom_app,
      Category.id_comp, Category.comp_id, NatTrans.naturality_assoc,
      Functor.comp_obj, Functor.id_obj]
    erw [adjM.left_triangle_components, Category.comp_id]
  rw [e]
  infer_instance

/-- The composition isomorphism of derived pullbacks commutes with the shifts. -/
instance commShift_leftDerivedUpperStarComp_hom {T S R : Scheme.{u}} (g₁ : T ⟶ S)
    (g₂ : S ⟶ R) : NatTrans.CommShift (leftDerivedUpperStarComp A g₁ g₂).hom ℤ := by
  have e : (leftDerivedUpperStarComp A g₁ g₂).hom =
      (leftDerivedUpperStarIsoMapDerivedCategory A (g₁ ≫ g₂)).hom ≫
        (Functor.mapDerivedCategoryNatIso (ProEtale.upperStarComp A g₁ g₂)).hom ≫
        ((g₂)^*[A].mapDerivedCategoryCompIso (g₁)^*[A]).hom ≫
        Functor.whiskerRight (leftDerivedUpperStarIsoMapDerivedCategory A g₂).inv D((g₁)^*[A]) ≫
        Functor.whiskerLeft L((g₂)^*[A]) (leftDerivedUpperStarIsoMapDerivedCategory A g₁).inv := by
    simp [leftDerivedUpperStarComp, leftDerivedUpperStarIsoMapDerivedCategory,
      Functor.leftDerivedFunctorNatIso, Functor.leftDerivedFunctorCompIso]
  have : NatTrans.CommShift (leftDerivedUpperStarIsoMapDerivedCategory A g₁).inv ℤ :=
    NatTrans.CommShift.of_iso_inv _ ℤ
  have : NatTrans.CommShift (leftDerivedUpperStarIsoMapDerivedCategory A g₂).inv ℤ :=
    NatTrans.CommShift.of_iso_inv _ ℤ
  rw [e]
  infer_instance

/-- Transport of the derived pullback along an equality of morphisms commutes with the
shifts. -/
instance commShift_leftDerivedUpperStarCongr_hom {X Y : Scheme.{u}} {f g : X ⟶ Y}
    (h : f = g) : NatTrans.CommShift (leftDerivedUpperStarCongr A h).hom ℤ := by
  subst h
  exact inferInstanceAs (NatTrans.CommShift (𝟙 _) ℤ)

/-- The square comparison of derived pullbacks commutes with the shifts. -/
instance commShift_leftDerivedUpperStarSquareIso_hom {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X}
    {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' f' f g) :
    NatTrans.CommShift (leftDerivedUpperStarSquareIso A sq).hom ℤ := by
  have : NatTrans.CommShift (leftDerivedUpperStarComp A f' g).inv ℤ :=
    NatTrans.CommShift.of_iso_inv _ ℤ
  dsimp only [leftDerivedUpperStarSquareIso, Iso.trans_hom, Iso.symm_hom]
  infer_instance

/-- The derived base change map `Lg^* Rf_* ⟶ Rf'_* Lg'^*` commutes with the shifts. -/
instance commShift_derivedBaseChangeMap {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X}
    {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' f' f g) :
    NatTrans.CommShift (derivedBaseChangeMap A sq) ℤ :=
  NatTrans.CommShift.mateEquiv (derivedUpperStarLowerStarAdjunction A f)
    (derivedUpperStarLowerStarAdjunction A f')
    (TwoSquare.mk _ _ _ _ (leftDerivedUpperStarSquareIso A sq).hom)

/-- A degree-one Ext identity after exact pullback gives the corresponding identity of morphisms
in the derived category, with the derived pullback, its shift isomorphism and the single-degree
comparison. Source: blueprint relative Kummer proof, Step 3
(blueprint: lem-pur-relative-kummer-exchange-from-conclusions). -/
theorem leftDerivedUpperStar_map_hom_of_ext_comp_eq.{w} {S T : Scheme.{u}} (u : T ⟶ S)
    [HasExt.{w} (Sheaf (ProEt.topology S) A)] [HasExt.{w} (Sheaf (ProEt.topology T) A)]
    {F G : Sheaf (ProEt.topology S) A} {F' G' : Sheaf (ProEt.topology T) A}
    (x : Ext.{w} F G 1) (y : Ext.{w} F' G' 1)
    (a : (ProEtale.upperStar A u).obj F ⟶ F') (b : (ProEtale.upperStar A u).obj G ⟶ G')
    (hxy : (x.mapExactFunctor (ProEtale.upperStar A u)).comp (Ext.mk₀ b) (add_zero 1) =
      (Ext.mk₀ a).comp y (zero_add 1)) :
    L((u)^*[A]).map x.hom ≫ (L((u)^*[A]).commShiftIso (1 : ℤ)).hom.app _ ≫
        ((singleFunctorCompLeftDerivedUpperStarIso A u).hom.app G ≫
          (DerivedCategory.singleFunctor _ 0).map b)⟦(1 : ℤ)⟧' =
      ((singleFunctorCompLeftDerivedUpperStarIso A u).hom.app F ≫
        (DerivedCategory.singleFunctor _ 0).map a) ≫ y.hom := by
  have h := congrArg Ext.hom hxy
  rw [Ext.comp_hom, Ext.comp_hom, Ext.mk₀_hom, Ext.mk₀_hom, Ext.mapExactFunctor_hom,
    ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp] at h
  have hc := NatTrans.shift_app_comm (leftDerivedUpperStarIsoMapDerivedCategory A u).hom
    (1 : ℤ) ((DerivedCategory.singleFunctor _ 0).obj G)
  have hn := (leftDerivedUpperStarIsoMapDerivedCategory A u).hom.naturality x.hom
  simp only [singleFunctorCompLeftDerivedUpperStarIso,
    Functor.singleFunctorCompLeftDerivedFunctorIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.map_comp, Category.assoc]
  dsimp only [leftDerivedUpperStarIsoMapDerivedCategory] at hc hn
  rw [reassoc_of% hc]
  erw [reassoc_of% hn]
  rw [← h]
  simp [ShiftedHom.map]

end AlgebraicGeometry.ProEtale
