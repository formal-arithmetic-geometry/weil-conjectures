/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.AdjunctionShift
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.UnitShift
public import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Shift

/-!
# The pro-étale derived base change map commutes with the shifts

For pro-étale sheaves with values in a Grothendieck abelian category `A`, the derived pullback
`Lg^*` carries the shift structure transported from `Rg_*` along the derived adjunction, while
`Rg_*` carries the shift structure transported from K-injective complexes. Using
`CategoryTheory.Adjunction.commShift_mapDerivedCategoryRightDerivedAdjunction`, we show:

* `AlgebraicGeometry.ProEtale.commShift_leftDerivedUpperStarIsoMapDerivedCategory_hom` and
  `AlgebraicGeometry.ProEtale.commShift_derivedBaseChangeMap`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Abelian

open scoped CategoryTheory.Functor

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
