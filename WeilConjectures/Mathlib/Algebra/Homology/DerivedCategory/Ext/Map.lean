/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors

/-!
# Functoriality of `Ext.mapExactFunctor` in the exact functor

`CategoryTheory.Abelian.Ext.mapExactFunctor` sends a class in `Ext^n (X, Y)` to a class in
`Ext^n (F X, F Y)`, for `F` an exact functor between abelian categories. This file shows
that this construction is functorial in `F`:

* `CategoryTheory.Abelian.Ext.mapExactFunctor_id`: the identity functor induces the
  identity map on `Ext`.
* `CategoryTheory.Abelian.Ext.mapExactFunctor_comp_functor`: mapping along `F ⋙ G` is
  mapping along `F` and then along `G`.
* `CategoryTheory.Abelian.Ext.mapExactFunctor_natIso`: an isomorphism `α : F ≅ G` of exact
  functors identifies mapping along `G` with mapping along `F`, conjugated by `α`.

All three are deduced from `CategoryTheory.Abelian.Ext.mapExactFunctor_hom'`, a variant of
`CategoryTheory.Abelian.Ext.mapExactFunctor_hom` in which the functor
`F.mapDerivedCategory` on derived categories is replaced by an arbitrary functor equipped
with an identification of the corresponding square of localizations; a class in `Ext` is
determined by the morphism it induces in the derived category.
-/

set_option maxSynthPendingDepth 3
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

@[expose] public section

universe t t' w w' w'' u u' u'' v v' v''

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
  CategoryTheory.DerivedCategory

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]
variable {E : Type u''} [Category.{v''} E] [Abelian E]

/-- A variant of `CategoryTheory.Abelian.Ext.mapExactFunctor_hom` in which the functor
`F.mapDerivedCategory` is replaced by an arbitrary functor `𝒢` between the derived
categories, together with an isomorphism `e` identifying
`F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ Q` with `Q ⋙ 𝒢`. -/
lemma Abelian.Ext.mapExactFunctor_hom' (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [HasDerivedCategory.{t} C] [HasDerivedCategory.{t'} D]
    [HasExt.{w} C] [HasExt.{w'} D] {X Y : C} {n : ℕ} (ε : Ext.{w} X Y n)
    (𝒢 : DerivedCategory C ⥤ DerivedCategory D) [𝒢.CommShift ℤ]
    (e : F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q (C := D) ≅
      DerivedCategory.Q (C := C) ⋙ 𝒢)
    [NatTrans.CommShift e.hom ℤ] :
    (ε.mapExactFunctor F).hom =
      (DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).app X).inv ≫
        e.hom.app ((CochainComplex.singleFunctor C 0).obj X)) ≫ ε.hom.map 𝒢 ≫
          (e.inv.app ((CochainComplex.singleFunctor C 0).obj Y) ≫ DerivedCategory.Q.map
            ((F.mapCochainComplexSingleFunctor 0).app Y).hom)⟦(n : ℤ)⟧' := by
  rw [← ShiftedHom.comp_mk₀ _ 0 rfl, ← ShiftedHom.mk₀_comp 0 rfl]
  exact LocalizerMorphism.equiv_smallShiftedHomMap
    (F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism (ComplexShape.up ℤ))
    DerivedCategory.Q DerivedCategory.Q ((F.mapCochainComplexSingleFunctor 0).app X)
      ((F.mapCochainComplexSingleFunctor 0).app Y) 𝒢 e ε

namespace Abelian.Ext

attribute [local instance] HasDerivedCategory.standard

/-- `Ext.mapExactFunctor` along the identity functor is the identity. -/
lemma mapExactFunctor_id [HasExt.{w} C] {X Y : C} {n : ℕ} (ε : Ext.{w} X Y n) :
    ε.mapExactFunctor (𝟭 C) = ε := by
  ext
  rw [Ext.mapExactFunctor_hom' (𝟭 C) ε (𝟭 (DerivedCategory C))
    (Functor.mapDerivedCategoryIdFactors C)]
  simp only [Functor.id_obj, Functor.comp_obj, Functor.mapCochainComplexSingleFunctor_id,
    Iso.app_inv, Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
    Functor.mapDerivedCategoryIdFactors, Iso.trans_hom, Functor.isoWhiskerRight_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    Functor.rightUnitor_inv_app, Category.comp_id, ← Functor.map_comp, Iso.inv_hom_id_app,
    Functor.map_id, ShiftedHom.id_map, Iso.trans_inv, Iso.symm_inv, Functor.isoWhiskerRight_inv,
    Category.assoc, Functor.rightUnitor_hom_app, Functor.leftUnitor_inv_app, Category.id_comp,
    Iso.app_hom, Functor.isoWhiskerLeft_hom]
  erw [Functor.map_id, Category.comp_id]

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits in
/-- `Ext.mapExactFunctor` is compatible with the composition of exact functors. -/
lemma mapExactFunctor_comp_functor (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [HasExt.{w} C] [HasExt.{w'} D] [HasExt.{w''} E] {X Y : C} {n : ℕ} (ε : Ext.{w} X Y n) :
    ε.mapExactFunctor (F ⋙ G) = (ε.mapExactFunctor F).mapExactFunctor G := by
  ext
  have h1 := Ext.mapExactFunctor_hom' (F ⋙ G) ε
    (F.mapDerivedCategory ⋙ G.mapDerivedCategory) (Functor.mapDerivedCategoryCompFactors F G)
  have h2 := Ext.mapExactFunctor_hom' G (ε.mapExactFunctor F) G.mapDerivedCategory
    G.mapDerivedCategoryFactors.symm
  have h3 := Ext.mapExactFunctor_hom' F ε F.mapDerivedCategory F.mapDerivedCategoryFactors.symm
  dsimp only [Functor.comp_obj] at h1 h2 h3 ⊢
  rw [h2, h3, h1]
  simp [ShiftedHom.map, Functor.mapDerivedCategoryCompFactors,
    Functor.mapCochainComplexSingleFunctor_comp, Functor.commShiftIso_comp_hom_app,
    CochainComplex.singleFunctor, CochainComplex.singleFunctors,
    Functor.shift_mapDerivedCategoryFactors_hom_naturality_assoc,
    Functor.mapDerivedCategoryFactors_inv_naturality_assoc]

/-- `Ext.mapExactFunctor` transported along an isomorphism `α : F ≅ G` of exact
functors: mapping along `G` is mapping along `F`, conjugated by `α`. -/
lemma mapExactFunctor_natIso {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [HasExt.{w} C] [HasExt.{w'} D] (α : F ≅ G) {X Y : C} {n : ℕ} (ε : Ext.{w} X Y n) :
    ε.mapExactFunctor G =
      ((mk₀ (α.inv.app X)).comp (ε.mapExactFunctor F) (zero_add n)).comp
        (mk₀ (α.hom.app Y)) (add_zero n) := by
  ext
  have hX : DerivedCategory.Q.map ((G.mapCochainComplexSingleFunctor 0).app X).inv ≫
        (Functor.mapDerivedCategoryNatIsoFactors α).hom.app
          ((CochainComplex.singleFunctor C 0).obj X) =
      DerivedCategory.Q.map ((CochainComplex.singleFunctor D 0).map (α.inv.app X) ≫
          ((F.mapCochainComplexSingleFunctor 0).app X).inv) ≫
        F.mapDerivedCategoryFactors.inv.app ((CochainComplex.singleFunctor C 0).obj X) := by
    rw [Functor.mapCochainComplexSingleFunctor_natIso α]
    simp [Functor.mapDerivedCategoryNatIsoFactors, ← Functor.map_comp_assoc,
      - Functor.map_comp]
  have hY : (Functor.mapDerivedCategoryNatIsoFactors α).inv.app
        ((CochainComplex.singleFunctor C 0).obj Y) ≫
      DerivedCategory.Q.map ((G.mapCochainComplexSingleFunctor 0).app Y).hom =
      F.mapDerivedCategoryFactors.hom.app ((CochainComplex.singleFunctor C 0).obj Y) ≫
        DerivedCategory.Q.map (((F.mapCochainComplexSingleFunctor 0).app Y).hom ≫
          (CochainComplex.singleFunctor D 0).map (α.hom.app Y)) := by
    rw [Functor.mapCochainComplexSingleFunctor_natIso α]
    simp [Functor.mapDerivedCategoryNatIsoFactors, ← Functor.map_comp]
  have h1 := Ext.mapExactFunctor_hom' G ε F.mapDerivedCategory
    (Functor.mapDerivedCategoryNatIsoFactors α)
  have h2 := Ext.mapExactFunctor_hom' F ε F.mapDerivedCategory
    F.mapDerivedCategoryFactors.symm
  dsimp only [Functor.comp_obj] at h1 h2 ⊢
  rw [Ext.comp_hom, Ext.comp_hom, h2, Ext.mk₀_hom, Ext.mk₀_hom, ShiftedHom.comp_mk₀,
    ShiftedHom.mk₀_comp, h1, hX, hY]
  simp [DerivedCategory.Q_map_singleFunctor_map]

end Abelian.Ext

end CategoryTheory

