/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerChernNormalizationData.DiagonalUniformizerLocalChernDefinitions
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteBoundaryExactTransport
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.FiniteExactArrow.FiniteExactArrowCalculus
public import WeilConjectures.AlgebraicGeometry.Cohomology.MayerVietorisExtFunctorSquare
public import WeilConjectures.CategoryTheory.Abelian.Ext.MapExactFunctorConj
public import WeilConjectures.Tactic.HEqCongr

/-! # Explicit composites of exact images of derived arrows

We record generic lemmas putting exact images of Ext classes and the finite comparison
isomorphisms into explicit composites, for use with the tactic `heq_congr`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

section Generic
open SpTowerClasses in
/-- The derived arrow of an Ext class precomposed with a unit, pushed through a square of exact
functors, then conjugated by endpoint maps. -/
theorem mk₀CompMk₀_mapExactFunctor_square_hom
    {C₁ C₂ C₃ C₄ : Type*} [Category C₁] [Category C₂] [Category C₃] [Category C₄]
    [Abelian C₁] [Abelian C₂] [Abelian C₃] [Abelian C₄]
    [HasExt C₁] [HasExt C₂] [HasExt C₄]
    [HasDerivedCategory C₁] [HasDerivedCategory C₃] [HasDerivedCategory C₄]
    (U : C₁ ⥤ C₂) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (G : C₂ ⥤ C₄) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (F : C₁ ⥤ C₃) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (V : C₃ ⥤ C₄) [V.Additive] [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (τ : U ⋙ G ≅ F ⋙ V) {P Q : C₁} {I : C₂} {I' : C₄} {P' : C₃}
    (gen : I ⟶ U.obj P) (a : I' ⟶ G.obj I) (c : F.obj P ≅ P') {n : ℕ} (x : Ext P Q n) :
    (Ext.mk₀CompMk₀ a (((Ext.mk₀ gen).comp (x.mapExactFunctor U) (zero_add n)).mapExactFunctor G)
      (τ.hom.app Q)).hom =
    (DerivedCategory.singleFunctor C₄ 0).map (a ≫ G.map gen ≫ τ.hom.app P ≫ V.map c.hom) ≫
      mapSingleArrow V n ((DerivedCategory.singleFunctor C₃ 0).map c.inv ≫
        mapSingleArrow F n x.hom) := by
  let := HasExt.standard C₃
  have hsq := CategoryTheory.Abelian.Ext.mapExactFunctor_square U F G V τ n x
  have h : Ext.mk₀CompMk₀ a
      (((Ext.mk₀ gen).comp (x.mapExactFunctor U) (zero_add n)).mapExactFunctor G)
      (τ.hom.app Q) = (Ext.mk₀ (a ≫ G.map gen ≫ τ.hom.app P)).comp
        ((x.mapExactFunctor F).mapExactFunctor V) (zero_add n) := by
    simp only [Ext.mk₀CompMk₀, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
      Ext.comp_assoc_of_third_deg_zero]
    rw [Iso.app_hom] at hsq
    rw [hsq, Ext.mk₀_comp_mk₀_assoc, Ext.mk₀_comp_mk₀_assoc, Iso.app_hom, Category.assoc]
  rw [h, mapSingleArrow_precompose, ← Functor.map_comp_assoc]
  simp only [Category.assoc, ← V.map_comp, Iso.hom_inv_id, V.map_id]
  erw [Category.comp_id]
  rw [SpTowerClasses.FiniteExactArrow.mapSingleArrow_ext,
    SpTowerClasses.FiniteExactArrow.mapSingleArrow_ext, Ext.comp_hom, Ext.mk₀_hom,
    ShiftedHom.mk₀_comp]
  rfl

open SpTowerClasses in
/-- A conjugated exact image of a single arrow, written as an explicit composite. -/
theorem map_comp_mapSingleArrow_eq {C D : Type*} [Category C] [Category D] [Abelian C]
    [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D] (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] {X Y : C} {X' : D} (c : F.obj X ≅ X')
    (n : ℤ) (f : (DerivedCategory.singleFunctor C 0).obj X ⟶
      ((DerivedCategory.singleFunctor C 0).obj Y)⟦n⟧) :
    (DerivedCategory.singleFunctor D 0).map c.inv ≫ mapSingleArrow F n f =
      ((DerivedCategory.singleFunctor D 0).map c.inv ≫
          (F.mapDerivedCategorySingleFunctor 0).inv.app X) ≫ F.mapDerivedCategory.map f ≫
        ((F.mapDerivedCategory.commShiftIso n).hom.app _ ≫
          ((F.mapDerivedCategorySingleFunctor 0).hom.app Y)⟦n⟧') := by
  simp only [mapSingleArrow, Category.assoc]

/-- The inverse of a whiskered single-object comparison followed by an endpoint isomorphism. -/
theorem compIsoApp_isoWhiskerRight_trans_mapIso_inv_heq {C D DC DD : Type*} [Category C]
    [Category D] [Category DC] [Category DD] {S S' : C ⥤ DC} (h : S' = S) (F' : DC ⥤ DD)
    {F : C ⥤ D} {T : D ⥤ DD} (φ : S ⋙ F' ≅ F ⋙ T) {X : C} {X' : D} (c : F.obj X ≅ X') :
    HEq (Functor.compIsoApp (Functor.isoWhiskerRight (eqToIso h) F' ≪≫ φ) X ≪≫ T.mapIso c).inv
      (T.map c.inv ≫ φ.inv.app X) := by
  subst h
  simp [Functor.compIsoApp]

/-- The shifted comparison of a single object with the identity endpoint. -/
theorem p1DecompositionShiftedComparison_hom_heq {C D DC DD : Type*} [Category C] [Category D]
    [Category DC] [Category DD] [HasShift DC ℤ] [HasShift DD ℤ] (F' : DC ⥤ DD) [F'.CommShift ℤ]
    (S : C ⥤ DC) (T : D ⥤ DD) (F : C ⥤ D) (φ : S ⋙ F' ≅ F ⋙ T) (L : C) (M : D)
    (hM : M = F.obj L) (e : F.obj L ≅ M) (he : HEq e (Iso.refl (F.obj L))) (n : ℤ) :
    HEq (Etale.p1DecompositionShiftedComparison F' S T F φ L M e n).hom
      ((F'.commShiftIso n).hom.app (S.obj L) ≫ (φ.hom.app L)⟦n⟧') := by
  subst hM
  obtain rfl := eq_of_heq he
  unfold Etale.p1DecompositionShiftedComparison
  simp

end Generic

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
