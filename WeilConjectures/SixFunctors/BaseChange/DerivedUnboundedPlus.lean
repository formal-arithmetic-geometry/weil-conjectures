/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Restrict
public import WeilConjectures.SixFunctors.BaseChange.DerivedComparison
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded

/-!
# The unbounded derived base change map restricts to the bounded below one

For a commutative square of schemes `g' ≫ f = f' ≫ g`, the derived base change map
`AlgebraicGeometry.Etale.derivedBaseChangeMap` on the unbounded derived categories, evaluated at
a bounded below complex `K`, is the bounded below derived base change map
`AlgebraicGeometry.Etale.baseChange` at `K`, modulo the identifications of the derived functors
on the bounded below derived categories with the restrictions of the unbounded ones. Both maps
are mates of the derived square isomorphisms, and the bounded below derived adjunctions are the
restrictions of the unbounded ones (`CategoryTheory.map_mateEquiv_app_of_restrict`).

## Main statements

- `AlgebraicGeometry.Etale.ι_map_baseChange_app`: the bounded below derived base change map is
  the restriction of the unbounded one.
- `AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_app_ι_iff`: the unbounded derived base
  change map is an isomorphism at a bounded below complex if and only if the bounded below one
  is.
-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits

open scoped CategoryTheory.Functor

namespace CategoryTheory.Functor

variable {C D E : Type*} [Category* C] [Category* D] [Category* E] [Abelian C] [Abelian D]
  [Abelian E] [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]

/-- The inverse of `Functor.mapDerivedCategoryPlusNatIso` is the restriction of the inverse of
`Functor.mapDerivedCategoryNatIso`. -/
@[simp]
lemma ι_map_mapDerivedCategoryPlusNatIso_inv_app {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] [PreservesFiniteLimits G]
    [PreservesFiniteColimits G] (e : F ≅ G) (X : DerivedCategory.Plus C) :
    DerivedCategory.Plus.ι.map ((mapDerivedCategoryPlusNatIso e).inv.app X) =
      (mapDerivedCategoryNatIso e).inv.app (DerivedCategory.Plus.ι.obj X) := by
  rw [← cancel_mono ((mapDerivedCategoryNatIso e).hom.app _), Iso.inv_hom_id_app,
    ← ι_map_mapDerivedCategoryPlusNatIso_hom_app, ← Functor.map_comp, Iso.inv_hom_id_app]
  exact DerivedCategory.Plus.ι.map_id _

/-- The inverse of `Functor.mapDerivedCategoryPlusCompIso` is the restriction of the inverse of
`Functor.mapDerivedCategoryCompIso`. -/
@[simp]
lemma ι_map_mapDerivedCategoryPlusCompIso_inv_app (F : C ⥤ D) (G : D ⥤ E) [F.Additive]
    [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] [PreservesFiniteLimits G]
    [PreservesFiniteColimits G] (X : DerivedCategory.Plus C) :
    DerivedCategory.Plus.ι.map ((mapDerivedCategoryPlusCompIso F G).inv.app X) =
      (mapDerivedCategoryCompIso F G).inv.app (DerivedCategory.Plus.ι.obj X) := by
  rw [← cancel_mono ((mapDerivedCategoryCompIso F G).hom.app _), Iso.inv_hom_id_app,
    ← ι_map_mapDerivedCategoryPlusCompIso_hom_app, ← Functor.map_comp, Iso.inv_hom_id_app]
  exact DerivedCategory.Plus.ι.map_id _

end CategoryTheory.Functor

namespace AlgebraicGeometry

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [HasSmallSiteSheafify A]

/-- The identification `ι ⋙ Lg^* ≅ D⁺(g^*) ⋙ ι` of the restriction of the unbounded derived
pullback to the bounded below derived category with the bounded below derived pullback. -/
noncomputable abbrev leftDerivedUpperStarPlusIso {Y Z : Scheme.{u}} (g : Z ⟶ Y) :
    DerivedCategory.Plus.ι ⋙ L((g)^*[A]) ≅ D+((g)^*[A]) ⋙ DerivedCategory.Plus.ι :=
  Functor.isoWhiskerLeft DerivedCategory.Plus.ι (leftDerivedUpperStarIsoMapDerivedCategory A g) ≪≫
    ((g)^*[A]).mapDerivedCategoryPlusCompatibility.symm

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

omit [HasSmallSiteSheafify A] in
/-- The pullback comparison `θ_sq` on the bounded below derived categories is the restriction of
the derived square isomorphism on the unbounded derived categories. -/
lemma ι_map_pullbackSquareComparison_hom_app (sq : CommSq g' f' f g)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology A)) :
    DerivedCategory.Plus.ι.map ((Etale.pullbackSquareComparison A sq).hom.app K) =
      (leftDerivedUpperStarPlusIso A f').inv.app (D+((g)^*[A]).obj K) ≫
        L((f')^*[A]).map ((leftDerivedUpperStarPlusIso A g).inv.app K) ≫
        (derivedSquareUpperStarIso A sq).hom.app (DerivedCategory.Plus.ι.obj K) ≫
        L((g')^*[A]).map ((leftDerivedUpperStarPlusIso A f).hom.app K) ≫
        (leftDerivedUpperStarPlusIso A g').hom.app (D+((f)^*[A]).obj K) := by
  rw [Etale.pullbackSquareComparison_eq]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp,
    upperStarCompDerivedPlus, Iso.trans_inv, Functor.ι_map_mapDerivedCategoryPlusNatIso_inv_app,
    Functor.ι_map_mapDerivedCategoryPlusCompIso_inv_app,
    Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app,
    Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app, Category.assoc]
  simp only [Functor.comp_obj, ObjectProperty.ι_obj, Functor.mapDerivedCategoryPlusCompatibility,
    Iso.refl_symm, Iso.refl_inv, NatTrans.id_app, leftDerivedUpperStarIsoMapDerivedCategory,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, CategoryTheory.Functor.map_id,
    derivedSquareUpperStarIso, leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
    Functor.leftDerivedFunctorCompIso, Iso.trans_assoc, Iso.symm_self_id_assoc, Iso.trans_symm,
    Iso.trans_hom, Iso.symm_hom, Iso.symm_inv, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
    Functor.whiskerRight_app, NatTrans.naturality, NatTrans.naturality_assoc, assoc, cancelIso,
    Iso.inv_hom_id_app_assoc, id_comp]
  erw [Iso.inv_hom_id_app_assoc, CategoryTheory.Functor.map_id]
  erw [Category.id_comp, Category.comp_id]

omit [HasSmallSiteSheafify A] in
/-- **The bounded below derived base change map is the restriction of the unbounded one.** For a
commutative square `g' ≫ f = f' ≫ g` and `K ∈ D⁺(X_ét)`, the derived base change map
`AlgebraicGeometry.Etale.baseChange` at `K` is the unbounded derived base change map
`AlgebraicGeometry.Etale.derivedBaseChangeMap` at `K`, modulo the identifications of the bounded
below derived functors with the restrictions of the unbounded ones. -/
lemma ι_map_baseChange_app (sq : CommSq g' f' f g)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A)) :
    DerivedCategory.Plus.ι.map ((Etale.baseChange A sq).app K) =
      (leftDerivedUpperStarPlusIso A g).inv.app (R+((f)_*[A]).obj K) ≫
        L((g)^*[A]).map (((f)_*[A]).rightDerivedFunctorPlusCompatibility.hom.app K) ≫
        (derivedBaseChangeMap A sq).app (DerivedCategory.Plus.ι.obj K) ≫
        R((f')_*[A]).map ((leftDerivedUpperStarPlusIso A g').hom.app K) ≫
        ((f')_*[A]).rightDerivedFunctorPlusCompatibility.inv.app (D+((g')^*[A]).obj K) := by
  rw [Etale.baseChange_app_eq_mateEquiv, ← Adjunction.derivedAdjunctionPlus_eq_derivedPlus,
    ← Adjunction.derivedAdjunctionPlus_eq_derivedPlus]
  exact map_mateEquiv_app_of_restrict (derivedUpperStarLowerStarAdjunction A f)
    (derivedUpperStarLowerStarAdjunction A f') _ _ (leftDerivedUpperStarPlusIso A f)
    ((f)_*[A]).rightDerivedFunctorPlusCompatibility.symm (leftDerivedUpperStarPlusIso A f')
    ((f')_*[A]).rightDerivedFunctorPlusCompatibility.symm (leftDerivedUpperStarPlusIso A g)
    (leftDerivedUpperStarPlusIso A g')
    (Adjunction.map_restrictFullyFaithful_ofNatIsoLeft_counit_app _ _ _ _ _ _)
    (Adjunction.map_restrictFullyFaithful_ofNatIsoLeft_unit_app _ _ _ _ _ _)
    (TwoSquare.mk _ _ _ _ (derivedSquareUpperStarIso A sq).hom) _
    (ι_map_pullbackSquareComparison_hom_app A sq) K

omit [HasSmallSiteSheafify A] in
/-- The unbounded derived base change map is an isomorphism at a bounded below complex if and
only if the bounded below derived base change map is. -/
theorem isIso_derivedBaseChangeMap_app_ι_iff (sq : CommSq g' f' f g)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A)) :
    IsIso ((derivedBaseChangeMap A sq).app (DerivedCategory.Plus.ι.obj K)) ↔
      IsIso ((Etale.baseChange A sq).app K) := by
  rw [← isIso_iff_of_reflects_iso _ DerivedCategory.Plus.ι, ι_map_baseChange_app,
    isIso_comp_left_iff, isIso_comp_left_iff, isIso_comp_right_iff]

end Etale

end AlgebraicGeometry
