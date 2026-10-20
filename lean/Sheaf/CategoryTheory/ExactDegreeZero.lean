/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M9
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor

/-!
# A named interface for exact functors on degree-zero objects

The object and morphism functions have their own names. In particular, comparing their
images under a localized functor does not require unfolding the single-degree functor.
The constructions are the canonical Mathlib single functor and its exact-functor comparison.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

namespace SheafExactDegreeZero

variable {V W X : Type*} [Category V] [Category W] [Category X]
  [Abelian V] [Abelian W] [Abelian X]
  [HasDerivedCategory V] [HasDerivedCategory W] [HasDerivedCategory X]

/-- The canonical degree-zero object, kept behind a named object function.
(blueprint: def-geo-exact-degree-zero-interface) -/
@[irreducible]
def obj (V : Type*) [Category V] [Abelian V] [HasDerivedCategory V] (M : V) :
    DerivedCategory V := (DerivedCategory.singleFunctor V 0).obj M

/-- The canonical degree-zero image of a morphism.
(blueprint: def-geo-exact-degree-zero-interface) -/
@[irreducible]
def map {M N : V} (f : M ⟶ N) : obj V M ⟶ obj V N := by
  unfold obj
  exact (DerivedCategory.singleFunctor V 0).map f

/-- The degree-zero functor with named object and morphism functions.
(blueprint: def-geo-exact-degree-zero-interface) -/
def functor (V : Type*) [Category V] [Abelian V] [HasDerivedCategory V] :
    V ⥤ DerivedCategory V where
  obj := obj V
  map := map
  map_id M := by
    unfold map obj
    exact (DerivedCategory.singleFunctor V 0).map_id M
  map_comp f g := by
    unfold map obj
    exact (DerivedCategory.singleFunctor V 0).map_comp f g

/-- The exact-functor comparison for the named degree-zero functor.
(blueprint: def-geo-exact-degree-zero-interface) -/
def comparison (F : V ⥤ W) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    functor V ⋙ F.mapDerivedCategory ≅ F ⋙ functor W := by
  let e := F.mapDerivedCategorySingleFunctor 0
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · refine ⟨?_, ?_, ?_, ?_⟩
    · unfold functor obj
      exact e.hom.app M
    · unfold functor obj
      exact e.inv.app M
    · unfold functor obj
      exact e.hom_inv_id_app M
    · unfold functor obj
      exact e.inv_hom_id_app M
  · intro M N f
    change F.mapDerivedCategory.map (map f) ≫ _ = _ ≫ map (F.map f)
    unfold map obj
    exact e.hom.naturality f

/-- The canonical derived unit attached to an ordinary morphism into an exact functor.
(blueprint: def-geo-exact-degree-zero-interface) -/
@[irreducible]
def unit (F : V ⥤ W) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {K : W} {M : V} (η : K ⟶ F.obj M) :
    obj W K ⟶ F.mapDerivedCategory.obj (obj V M) :=
  map η ≫ (comparison F).inv.app M

/-- The named derived unit represents extension to arbitrary unbounded test objects.
(blueprint: def-geo-exact-degree-zero-interface) -/
def Universal (F : V ⥤ W) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {K : W} {M : V} (η : K ⟶ F.obj M) : Prop :=
  ∀ N : DerivedCategory V,
    Function.Bijective (fun f : obj V M ⟶ N ↦ unit F η ≫ F.mapDerivedCategory.map f)

/-- The named interface has the same objects as the usual single functor.
(blueprint: def-geo-exact-degree-zero-interface) -/
theorem obj_eq (M : V) : obj V M = (DerivedCategory.singleFunctor V 0).obj M := by
  unfold obj
  rfl

/-- Degree-zero maps preserve composition.
(blueprint: def-geo-exact-degree-zero-interface) -/
theorem map_comp {M N P : V} (f : M ⟶ N) (g : N ⟶ P) :
    map (f ≫ g) = map f ≫ map g := by
  unfold map obj
  exact (DerivedCategory.singleFunctor V 0).map_comp f g

/-- Degree-zero maps preserve identities.
(blueprint: def-geo-exact-degree-zero-interface) -/
theorem map_id (M : V) : map (𝟙 M) = 𝟙 (obj V M) := by
  unfold map obj
  exact (DerivedCategory.singleFunctor V 0).map_id M

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- Compatibility with the canonical composition and isomorphism comparisons.
Source: Mathlib exact-functor single comparison and the source library's single coherence.
(blueprint: def-geo-exact-degree-zero-interface) -/
theorem comparison_comp (F : V ⥤ W) (G : W ⥤ X) (H : V ⥤ X)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : F ⋙ G ≅ H) (M : V) :
    (comparison G).inv.app (F.obj M) ≫
      G.mapDerivedCategory.map ((comparison F).inv.app M) ≫
      (Functor.mapDerivedCategoryCompIso F G).inv.app (obj V M) ≫
      (Functor.mapDerivedCategoryNatIso e).hom.app (obj V M) =
    map (e.hom.app M) ≫ (comparison H).inv.app M := by
  unfold comparison functor map obj
  change (G.mapDerivedCategorySingleFunctor 0).inv.app (F.obj M) ≫
    G.mapDerivedCategory.map ((F.mapDerivedCategorySingleFunctor 0).inv.app M) ≫
    (Functor.mapDerivedCategoryCompIso F G).inv.app _ ≫
    (Functor.mapDerivedCategoryNatIso e).hom.app _ =
    (DerivedCategory.singleFunctor X 0).map (e.hom.app M) ≫
      (H.mapDerivedCategorySingleFunctor 0).inv.app M
  rw [← cancel_mono ((H.mapDerivedCategorySingleFunctor 0).hom.app M)]
  simp only [Category.assoc]
  rw [Functor.mapDerivedCategoryNatIso_hom_app_singleFunctor,
    ← Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor F G M]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp,
    Iso.inv_hom_id_app_assoc, Category.comp_id]

/-- Units of exact functors respect a specified composition isomorphism.
(blueprint: def-geo-exact-degree-zero-interface) -/
theorem unit_comp (F : V ⥤ W) (G : W ⥤ X) (H : V ⥤ X)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : F ⋙ G ≅ H)
    (eD : F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ H.mapDerivedCategory)
    (heD : eD = (Functor.mapDerivedCategoryCompIso F G).symm ≪≫
      Functor.mapDerivedCategoryNatIso e)
    {K : X} {L : W} {M : V}
    (f : K ⟶ G.obj L) (g : L ⟶ F.obj M) (h : K ⟶ H.obj M)
    (hh : h = f ≫ G.map g ≫ e.hom.app M) :
    unit H h = unit G f ≫ G.mapDerivedCategory.map (unit F g) ≫
      eD.hom.app (obj V M) := by
  subst eD
  unfold unit
  subst h
  simp only [map_comp, Functor.map_comp, Category.assoc,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  have hn := (comparison G).inv.naturality g
  change map (G.map g) ≫ (comparison G).inv.app (F.obj M) =
    (comparison G).inv.app L ≫ G.mapDerivedCategory.map (map g) at hn
  rw [← reassoc_of% hn, comparison_comp F G H e M]

set_option backward.isDefEq.respectTransparency false in
private theorem derived_id_single {V : Type*} [Category V] [Abelian V]
    [HasDerivedCategory V] (X : V) :
    (Functor.mapDerivedCategoryIdIso V).hom.app ((DerivedCategory.singleFunctor V 0).obj X) =
      ((𝟭 V).mapDerivedCategorySingleFunctor 0).hom.app X := by
  rw [Functor.mapDerivedCategorySingleFunctor_hom_app_eq]
  have hi := congr_app (congr_arg Iso.hom (Functor.mapDerivedCategoryIdIso_factorsh V))
    (((HomotopyCategory.singleFunctors V).functor 0).obj X)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    Functor.mapHomotopyCategoryIdIso_hom_app_eq_id] at hi
  dsimp at hi
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at hi
  rw [hi]
  change (𝟭 V).mapDerivedCategoryFactorsh.hom.app
    ((HomotopyCategory.quotient V (.up ℤ)).obj
      ((HomologicalComplex.single V (.up ℤ) 0).obj X)) ≫ 𝟙 _ ≫ 𝟙 _ = _
  simp only [Category.comp_id]
  erw [Functor.mapDerivedCategoryFactorsh_hom_app]
  simp only [Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv]
  have hq (K : CochainComplex V ℤ) :
      (DerivedCategory.quotientCompQhIso V).hom.app K = 𝟙 _ := by
    exact Quotient.lift.isLift_hom _ _ _ K
  have hq' (K : CochainComplex V ℤ) :
      (DerivedCategory.quotientCompQhIso V).inv.app K = 𝟙 _ := by
    exact Quotient.lift.isLift_inv _ _ _ K
  rw [hq, hq']
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id, Category.comp_id]
  have hs : (HomologicalComplex.singleMapHomologicalComplex (𝟭 V) (.up ℤ) 0).hom.app X =
      𝟙 _ := by
    change (HomologicalComplex.singleMapHomologicalComplex (𝟭 V) (.up ℤ) 0).hom.app X =
      𝟙 ((HomologicalComplex.single V (.up ℤ) 0).obj X)
    ext n
    by_cases hn : n = 0
    · subst n
      simp only [HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
        Functor.id_map, Functor.id_obj, Iso.hom_inv_id, HomologicalComplex.id_f]
    · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 X n hn).eq_of_src _ _
  change _ = _ ≫ DerivedCategory.Q.map
    ((HomologicalComplex.singleMapHomologicalComplex (𝟭 V) (.up ℤ) 0).hom.app X)
  rw [hs]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]


private theorem raw_unit_id
    {V : Type*} [Category V] [Abelian V] [HasDerivedCategory V]
    (F : V ⥤ V) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (e : F ≅ 𝟭 V) (M : V) (f : M ⟶ F.obj M) (hf : f = e.inv.app M) :
    (DerivedCategory.singleFunctor V 0).map f ≫
      (F.mapDerivedCategorySingleFunctor 0).inv.app M =
    (Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso V).inv.app
      ((DerivedCategory.singleFunctor V 0).obj M) := by
  rw [← cancel_mono ((Functor.mapDerivedCategoryNatIso e ≪≫
    Functor.mapDerivedCategoryIdIso V).hom.app
      ((DerivedCategory.singleFunctor V 0).obj M)), Iso.inv_hom_id_app]
  change ((DerivedCategory.singleFunctor V 0).map f ≫
    (F.mapDerivedCategorySingleFunctor 0).inv.app M) ≫
    (Functor.mapDerivedCategoryNatIso e).hom.app _ ≫
    (Functor.mapDerivedCategoryIdIso V).hom.app _ = _
  rw [derived_id_single]
  simp only [Category.assoc]
  rw [Functor.mapDerivedCategoryNatIso_hom_app_singleFunctor]
  simp only [hf, Iso.inv_hom_id_app_assoc, ← Functor.map_comp,
    Iso.inv_hom_id_app]
  change (DerivedCategory.singleFunctor V 0).map (𝟙 M) =
    𝟙 ((DerivedCategory.singleFunctor V 0).obj M)
  exact (DerivedCategory.singleFunctor V 0).map_id M

/-- The named exact unit is normalized by the canonical derived identity comparison.
(blueprint: def-geo-exact-degree-zero-interface) -/
theorem unit_id (F : V ⥤ V) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (e : F ≅ 𝟭 V) (M : V) (f : M ⟶ F.obj M) (hf : f = e.inv.app M) :
    unit F f =
      (Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso V).inv.app
        (obj V M) := by
  unfold unit map comparison functor obj
  exact raw_unit_id F e M f hf

/-- The named universal property is exactly the usual single-functor formula.
The two formulas differ only by associativity of composition.
(blueprint: def-geo-exact-degree-zero-interface) -/
theorem universal_iff (F : V ⥤ W) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {K : W} {M : V} (η : K ⟶ F.obj M) :
    Universal F η ↔ ∀ N : DerivedCategory V,
      Function.Bijective (fun f : (DerivedCategory.singleFunctor V 0).obj M ⟶ N ↦
        (DerivedCategory.singleFunctor W 0).map η ≫
          (F.mapDerivedCategorySingleFunctor 0).inv.app M ≫ F.mapDerivedCategory.map f) := by
  unfold Universal unit map comparison functor obj
  change (∀ N : DerivedCategory V,
    Function.Bijective (fun f : (DerivedCategory.singleFunctor V 0).obj M ⟶ N ↦
      ((DerivedCategory.singleFunctor W 0).map η ≫
        (F.mapDerivedCategorySingleFunctor 0).inv.app M) ≫ F.mapDerivedCategory.map f)) ↔ _
  simp only [Category.assoc]

universe u

/-- Sheafification on an essentially small module site, used without searching for an
arbitrary right-adjoint decomposition of the sheaf inclusion.
(blueprint: def-geo-exact-degree-zero-interface) -/
theorem scalarWeakSheafify {C : Type (u + 1)} [Category.{u} C]
    [EssentiallySmall.{u + 1} C] (J : GrothendieckTopology C)
    (R : Type (u + 1)) [CommRing R] : HasWeakSheafify J (ModuleCat.{u + 1} R) :=
  HasSheafify.isRightAdjoint

/-- The canonical degree-zero sheaf object, with the site's derived-category data fixed once.
(blueprint: def-geo-exact-degree-zero-interface) -/
def scalarObj {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) (R : Type (u + 1)) [CommRing R]
    (M : Sheaf J (ModuleCat.{u + 1} R)) :
    DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)) :=
  obj (Sheaf J (ModuleCat.{u + 1} R)) M

/-- The canonical degree-zero scalar unit, with its restriction functor fixed on a general site.
(blueprint: def-geo-exact-degree-zero-interface) -/
@[irreducible]
def scalarUnit {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) (F : Sheaf J (ModuleCat.{u + 1} R))
    (G : Sheaf J (ModuleCat.{u + 1} S))
    (η : F ⟶ (Sheaf.restrictScalars J φ).obj G) :
    scalarObj J R F ⟶ (Sheaf.derivedRestrictScalars J φ).obj (scalarObj J S G) :=
  unit (Sheaf.restrictScalars J φ) η

/-- The unbounded universal property of the canonical scalar unit on a general site.
(blueprint: def-geo-exact-degree-zero-interface) -/
def scalarUniversal {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) (F : Sheaf J (ModuleCat.{u + 1} R))
    (G : Sheaf J (ModuleCat.{u + 1} S))
    (η : F ⟶ (Sheaf.restrictScalars J φ).obj G) : Prop :=
  Sheaf.IsDerivedBaseChange (scalarUnit J φ F G η)

/-- The site specialization retains precisely the original raw single-functor formula.
(blueprint: def-geo-exact-degree-zero-interface) -/
theorem scalarUniversal_iff {C : Type (u + 1)} [Category.{u} C]
    [EssentiallySmall.{u + 1} C] (J : GrothendieckTopology C)
    {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) (F : Sheaf J (ModuleCat.{u + 1} R))
    (G : Sheaf J (ModuleCat.{u + 1} S))
    (η : F ⟶ (Sheaf.restrictScalars J φ).obj G) :
    scalarUniversal J φ F G η ↔ ∀ N : DerivedCategory (Sheaf J (ModuleCat.{u + 1} S)),
      Function.Bijective (fun f : (DerivedCategory.singleFunctor _ 0).obj G ⟶ N ↦
        (DerivedCategory.singleFunctor _ 0).map η ≫
          ((Sheaf.restrictScalars J φ).mapDerivedCategorySingleFunctor 0).inv.app G ≫
            (Sheaf.restrictScalars J φ).mapDerivedCategory.map f) := by
  unfold scalarUniversal scalarUnit scalarObj
  change Universal (Sheaf.restrictScalars J φ) η ↔ _
  exact universal_iff (Sheaf.restrictScalars J φ) η

end SheafExactDegreeZero
