/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-!
# Restriction of scalars and the connecting morphisms of short exact sequences

For an exact functor `F`, the isomorphisms `(F Z)[0] ≅ F(Z[0])`
(`CategoryTheory.Functor.mapDerivedCategorySingleFunctorObjIso`) are compatible with the
connecting morphisms of short exact sequences
(`ShortComplex.ShortExact.mapDerivedCategorySingleFunctorObjIso_hom_comp_map_singleδ_of_heq`).
For the restriction of scalars of sheaves of modules along `f : A →+* A'` this is stated with
the derived restriction of scalars `CategoryTheory.Sheaf.derivedRestrictScalars`
(`CategoryTheory.Sheaf.derivedRestrictScalars_map_singleδ_of_heq`), with all objects given
separately, so that it can be instantiated with any presentation of them.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace CategoryTheory

namespace ShortComplex.ShortExact

variable {C D : Type*} [Category* C] [Abelian C] [Category* D] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] (F : C ⥤ D) [F.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F] {S : ShortComplex C} (hS : S.ShortExact)

/-- The isomorphism `(F Z)[0] ≅ F(Z[0])` of an exact functor `F` with the inclusions in degree
`n`, stated objectwise (the inverse of `Functor.mapDerivedCategorySingleFunctor`). -/
noncomputable def _root_.CategoryTheory.Functor.mapDerivedCategorySingleFunctorObjIso (n : ℤ)
    (Z : C) :
    (DerivedCategory.singleFunctor D n).obj (F.obj Z) ≅
      F.mapDerivedCategory.obj ((DerivedCategory.singleFunctor C n).obj Z) :=
  ((F.mapDerivedCategorySingleFunctor n).app Z).symm

@[simp]
lemma _root_.CategoryTheory.Functor.mapDerivedCategorySingleFunctorObjIso_hom (n : ℤ) (Z : C) :
    (F.mapDerivedCategorySingleFunctorObjIso n Z).hom =
      (F.mapDerivedCategorySingleFunctor n).inv.app Z :=
  rfl

/-- An exact functor `F` commutes with the connecting morphisms of a short exact sequence `S`,
through the isomorphisms `F(Z[0]) ≅ (F Z)[0]`, stated with objects `Z₁ = S.X₁`, `Z₃ = S.X₃` and
connecting morphisms `δ`, `δF` given separately (so that it can be instantiated with any
presentation of them). -/
lemma mapDerivedCategorySingleFunctor_inv_comp_map_singleδ_of_heq {Z₁ Z₃ : C}
    (f₁ : S.X₁ = Z₁) (f₃ : S.X₃ = Z₃)
    (δ : (DerivedCategory.singleFunctor C 0).obj Z₃ ⟶
      ((DerivedCategory.singleFunctor C 0).obj Z₁)⟦(1 : ℤ)⟧) (hδ : HEq δ hS.singleδ)
    (δF : (DerivedCategory.singleFunctor D 0).obj (F.obj Z₃) ⟶
      ((DerivedCategory.singleFunctor D 0).obj (F.obj Z₁))⟦(1 : ℤ)⟧)
    (hδF : HEq δF (hS.map_of_exact F).singleδ) :
    (F.mapDerivedCategorySingleFunctor 0).inv.app Z₃ ≫ F.mapDerivedCategory.map δ ≫
        (F.mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app _ =
      δF ≫ ((F.mapDerivedCategorySingleFunctor 0).inv.app Z₁)⟦(1 : ℤ)⟧' := by
  subst f₁ f₃
  obtain rfl := eq_of_heq hδ
  obtain rfl := eq_of_heq hδF
  have h₂ := hS.mapShiftedHom_singleδ F
  simp only [ShiftedHom.map] at h₂
  rw [h₂, Iso.inv_hom_id_app_assoc]

/-- The form of
`CategoryTheory.ShortComplex.ShortExact.mapDerivedCategorySingleFunctor_inv_comp_map_singleδ_of_heq`
with the isomorphisms `Functor.mapDerivedCategorySingleFunctorObjIso`. -/
lemma mapDerivedCategorySingleFunctorObjIso_hom_comp_map_singleδ_of_heq {Z₁ Z₃ : C}
    (f₁ : S.X₁ = Z₁) (f₃ : S.X₃ = Z₃)
    (δ : (DerivedCategory.singleFunctor C 0).obj Z₃ ⟶
      ((DerivedCategory.singleFunctor C 0).obj Z₁)⟦(1 : ℤ)⟧) (hδ : HEq δ hS.singleδ)
    (δF : (DerivedCategory.singleFunctor D 0).obj (F.obj Z₃) ⟶
      ((DerivedCategory.singleFunctor D 0).obj (F.obj Z₁))⟦(1 : ℤ)⟧)
    (hδF : HEq δF (hS.map_of_exact F).singleδ) :
    (F.mapDerivedCategorySingleFunctorObjIso 0 Z₃).hom ≫ F.mapDerivedCategory.map δ ≫
        (F.mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app _ =
      δF ≫ ((F.mapDerivedCategorySingleFunctorObjIso 0 Z₁).hom)⟦(1 : ℤ)⟧' :=
  hS.mapDerivedCategorySingleFunctor_inv_comp_map_singleδ_of_heq F f₁ f₃ δ hδ δF hδF

end ShortComplex.ShortExact

namespace Sheaf

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) {A A' : Type (u + 1)} [CommRing A] [CommRing A'] (f : A →+* A')

/-- The restriction of scalars along `f` commutes with the connecting morphisms of a short exact
sequence `S` of sheaves of `A'`-modules, through isomorphisms `i₁, i₃` of the form
`(Res Z)[0] ≅ Res (Z[0])`, stated with the derived restriction of scalars
`Sheaf.derivedRestrictScalars` and with all objects and morphisms given separately (so that it
can be instantiated with any presentation of them). -/
lemma derivedRestrictScalars_map_singleδ_of_heq
    {S : ShortComplex (Sheaf J (ModuleCat.{u + 1} A'))} (hS : S.ShortExact)
    {Z₁ Z₃ : Sheaf J (ModuleCat.{u + 1} A')} {Y₁ Y₃ : Sheaf J (ModuleCat.{u + 1} A)}
    (f₁ : S.X₁ = Z₁) (f₃ : S.X₃ = Z₃)
    (g₁ : (restrictScalars J f).obj Z₁ = Y₁) (g₃ : (restrictScalars J f).obj Z₃ = Y₃)
    (i₁ : (DerivedCategory.singleFunctor _ 0).obj Y₁ ≅
      (derivedRestrictScalars J f).obj ((DerivedCategory.singleFunctor _ 0).obj Z₁))
    (hi₁ : HEq i₁ ((restrictScalars J f).mapDerivedCategorySingleFunctorObjIso 0 Z₁))
    (i₃ : (DerivedCategory.singleFunctor _ 0).obj Y₃ ≅
      (derivedRestrictScalars J f).obj ((DerivedCategory.singleFunctor _ 0).obj Z₃))
    (hi₃ : HEq i₃ ((restrictScalars J f).mapDerivedCategorySingleFunctorObjIso 0 Z₃))
    (δ : (DerivedCategory.singleFunctor _ 0).obj Z₃ ⟶
      ((DerivedCategory.singleFunctor _ 0).obj Z₁)⟦(1 : ℤ)⟧) (hδ : HEq δ hS.singleδ)
    (δF : (DerivedCategory.singleFunctor _ 0).obj Y₃ ⟶
      ((DerivedCategory.singleFunctor _ 0).obj Y₁)⟦(1 : ℤ)⟧)
    (hδF : HEq δF (hS.map_of_exact (restrictScalars J f)).singleδ) :
    i₃.hom ≫ (derivedRestrictScalars J f).map δ ≫
        ((derivedRestrictScalars J f).commShiftIso (1 : ℤ)).hom.app _ =
      δF ≫ i₁.hom⟦(1 : ℤ)⟧' := by
  subst f₁ f₃ g₁ g₃
  obtain rfl := eq_of_heq hi₁
  obtain rfl := eq_of_heq hi₃
  exact hS.mapDerivedCategorySingleFunctorObjIso_hom_comp_map_singleδ_of_heq _ rfl rfl δ hδ δF hδF

end Sheaf

end CategoryTheory
