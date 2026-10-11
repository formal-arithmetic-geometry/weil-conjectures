/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.ExactFunctorShift
public import WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
public import WeilConjectures.SixFunctors.Etale.Derived.Shift

/-!
# Compatibility of the derived pullback–pushforward adjunction with shifts

The shifts on the derived pullback `Lg^*` and pushforward `Rg_*` of étale sheaves
(`WeilConjectures.SixFunctors.Etale.Derived.Shift`) are transported from the functor `D(g^*)`
induced by the exact pullback and from its adjunction `D(g^*) ⊣ Rg_*`. This file shows that the
derived adjunction `Lg^* ⊣ Rg_*` is compatible with these shifts: its unit is the unit of
`D(g^*) ⊣ Rg_*` corrected by the identification `Lg^* ≅ D(g^*)`. Consequently the composition
isomorphisms of derived pullbacks, the derived square isomorphisms and the derived base change
map `Ex_* : Lg^* Rf_* ⟶ Rf'_* Lg'^*`, a mate of a square isomorphism, commute with shifts.

## Main statements

- `AlgebraicGeometry.Etale.commShift_derivedUpperStarLowerStarAdjunction`
- `AlgebraicGeometry.Etale.commShift_leftDerivedUpperStarComp_hom`
- `AlgebraicGeometry.Etale.commShift_derivedBaseChangeMap`
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [HasSmallSiteSheafify A]
variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

omit [HasSmallSiteSheafify A] in
/-- The unit of the derived adjunction `Lg^* ⊣ Rg_*` is the unit of `D(g^*) ⊣ Rg_*` followed by
the identification `D(g^*) ≅ Lg^*`: both are characterized by the unit of `g^* ⊣ g_*` on the
images of complexes (`CategoryTheory.Adjunction.derivedη_fac_app`). -/
theorem derivedUpperStarLowerStarAdjunction_unit :
    (derivedUpperStarLowerStarAdjunction A g).unit =
      (mapDerivedUpperStarLowerStarAdjunction A g).unit ≫
        Functor.whiskerRight (leftDerivedUpperStarIsoMapDerivedCategory A g).inv R((g)_*[A]) := by
  refine Functor.leftDerived_ext (L((g)^*[A]) ⋙ R((g)_*[A]))
    ((Functor.associator _ _ _).inv ≫
      Functor.whiskerRight ((g)^*[A]).leftDerivedFunctorCounit R((g)_*[A]))
    (HomotopyCategory.quasiIso _ (.up ℤ)) _ _ _ ?_
  ext X
  have h₁ := (((Etale.upperStarLowerStarAdjunction A g).mapHomotopyCategory
    (ComplexShape.up ℤ))).derivedη_fac_app (HomotopyCategory.quasiIso _ (.up ℤ))
    ((g)^*[A]).leftDerivedFunctorCounit ((g)_*[A]).rightDerivedFunctorUnit X
  have h₂ := (((Etale.upperStarLowerStarAdjunction A g).mapHomotopyCategory
    (ComplexShape.up ℤ))).derivedη_fac_app (HomotopyCategory.quasiIso _ (.up ℤ))
    ((g)^*[A]).mapDerivedCategoryFactorsh.hom ((g)_*[A]).rightDerivedFunctorUnit X
  have h₃ := congr_app ((g)^*[A]).leftDerivedFunctorIsoMapDerivedCategory_hom_fac X
  dsimp at h₁ h₂ h₃ ⊢
  simp only [derivedUpperStarLowerStarAdjunction, Adjunction.derivedAdjunction,
    mapDerivedUpperStarLowerStarAdjunction, Adjunction.mapDerivedCategoryRightDerivedAdjunction,
    Adjunction.derived_unit, Category.id_comp, Category.assoc]
  rw [h₁, ← h₃, leftDerivedUpperStarIsoMapDerivedCategory, ← Functor.map_comp,
    Iso.inv_hom_id_app_assoc, h₂]

/-- The derived adjunction `Lg^* ⊣ Rg_*` is compatible with the shifts. -/
instance commShift_derivedUpperStarLowerStarAdjunction :
    (derivedUpperStarLowerStarAdjunction A g).CommShift ℤ := by
  have := (mapDerivedUpperStarLowerStarAdjunction A g).commShift_of_leftAdjoint ℤ
  have : NatTrans.CommShift (leftDerivedUpperStarIsoMapDerivedCategory A g).inv ℤ :=
    Functor.CommShift.ofIso_compatibility (leftDerivedUpperStarIsoMapDerivedCategory A g).symm ℤ
  refine Adjunction.CommShift.mk' _ _ ?_
  rw [derivedUpperStarLowerStarAdjunction_unit]
  infer_instance

/-- The identification `Lg^* ≅ D(g^*)` commutes with the shifts, by definition of the shift on
`Lg^*`. -/
instance commShift_leftDerivedUpperStarIsoMapDerivedCategory_inv :
    NatTrans.CommShift (leftDerivedUpperStarIsoMapDerivedCategory A g).inv ℤ :=
  Functor.CommShift.ofIso_compatibility (leftDerivedUpperStarIsoMapDerivedCategory A g).symm ℤ

/-- The identification `Lg^* ≅ D(g^*)` commutes with the shifts. -/
instance commShift_leftDerivedUpperStarIsoMapDerivedCategory_hom :
    NatTrans.CommShift (leftDerivedUpperStarIsoMapDerivedCategory A g).hom ℤ :=
  have : NatTrans.CommShift (leftDerivedUpperStarIsoMapDerivedCategory A g).symm.hom ℤ :=
    commShift_leftDerivedUpperStarIsoMapDerivedCategory_inv A g
  NatTrans.CommShift.of_iso_inv (leftDerivedUpperStarIsoMapDerivedCategory A g).symm ℤ

variable {T S R : Scheme.{u}}

omit [HasSmallSiteSheafify A] in
/-- The composition isomorphism `L(g₁ ≫ g₂)^* ≅ Lg₂^* ⋙ Lg₁^*` of derived pullbacks, through
the identifications with the functors induced on derived categories. -/
lemma leftDerivedUpperStarComp_hom (g₁ : T ⟶ S) (g₂ : S ⟶ R) (g₁₂ : T ⟶ R)
    (hg₁₂ : g₁₂ = g₁ ≫ g₂) :
    (leftDerivedUpperStarComp A g₁ g₂ g₁₂ hg₁₂).hom =
      (leftDerivedUpperStarIsoMapDerivedCategory A g₁₂).hom ≫
        (Functor.mapDerivedCategoryNatIso (Etale.upperStarComp A g₁ g₂ g₁₂ hg₁₂)).hom ≫
        (Functor.mapDerivedCategoryCompIso _ _).hom ≫
        Functor.whiskerRight (leftDerivedUpperStarIsoMapDerivedCategory A g₂).inv
          D((g₁)^*[A]) ≫
        Functor.whiskerLeft L((g₂)^*[A]) (leftDerivedUpperStarIsoMapDerivedCategory A g₁).inv := by
  ext K
  simp [leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
    Functor.leftDerivedFunctorCompIso, leftDerivedUpperStarIsoMapDerivedCategory]

/-- The composition isomorphism of derived pullbacks commutes with the shifts. -/
instance commShift_leftDerivedUpperStarComp_hom (g₁ : T ⟶ S) (g₂ : S ⟶ R) (g₁₂ : T ⟶ R)
    (hg₁₂ : g₁₂ = g₁ ≫ g₂) :
    NatTrans.CommShift (leftDerivedUpperStarComp A g₁ g₂ g₁₂ hg₁₂).hom ℤ := by
  rw [leftDerivedUpperStarComp_hom]
  infer_instance


variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- The derived square isomorphism `Lg^* ⋙ Lf'^* ≅ Lf^* ⋙ Lg'^*` commutes with the shifts. -/
instance commShift_derivedSquareUpperStarIso_hom (sq : CommSq g' f' f g) :
    NatTrans.CommShift (derivedSquareUpperStarIso A sq).hom ℤ := by
  have := commShift_leftDerivedUpperStarComp_hom A f' g (g' ≫ f) sq.w
  have : NatTrans.CommShift (leftDerivedUpperStarComp A f' g (g' ≫ f) sq.w).inv ℤ :=
    NatTrans.CommShift.of_iso_inv _ ℤ
  dsimp only [derivedSquareUpperStarIso, Iso.trans_hom, Iso.symm_hom]
  infer_instance

/-- The derived base change map `Ex_* : Lg^* Rf_* ⟶ Rf'_* Lg'^*` commutes with the shifts: it is
the mate of the derived square isomorphism with respect to adjunctions compatible with shifts. -/
instance commShift_derivedBaseChangeMap (sq : CommSq g' f' f g) :
    NatTrans.CommShift (derivedBaseChangeMap A sq) ℤ :=
  NatTrans.CommShift.mateEquiv (derivedUpperStarLowerStarAdjunction A f)
    (derivedUpperStarLowerStarAdjunction A f') _

end AlgebraicGeometry.Etale
