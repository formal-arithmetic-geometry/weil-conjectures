/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Dualizable
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsIhomProjection

/-!
# The left projection morphism of a derived monoidal adjunction

Let `F : C ⥤ D` be a strong monoidal functor between monoidal Grothendieck abelian categories
with functorial flat resolutions, which preserves flat objects and the quasi-isomorphisms between
K-flat complexes, with an exact right adjoint `G`. The left derived functor `LF` is monoidal
(`CategoryTheory.Functor.leftDerivedFunctorMonoidal`), and for any adjunction
`LF ⊣ D(G)` whose unit and counit are computed on the image of complexes by those of `F ⊣ G`,
the left projection morphism `K ⊗ᴸ D(G) N ⟶ D(G) (LF K ⊗ᴸ N)`
(`CategoryTheory.Adjunction.leftProjectionMorphism`) is computed, on the image of complexes and
modulo comparison maps, by the left projection morphism of the adjunction induced on homotopy
categories. Consequently, if `N` is the image of a complex `Z` such that the left projection
morphisms `B ⊗ G Z^q ⟶ G (F B ⊗ Z^q)` of `F ⊣ G` are isomorphisms, then so are the left
projection morphisms `K ⊗ᴸ D(G) N ⟶ D(G) (LF K ⊗ᴸ N)`.

This is the left-handed analogue of
`WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsIhomProjection`, for an
arbitrary monoidal adjunction with exact right adjoint.

## Main results

- `CategoryTheory.Adjunction.leftProjectionMorphism_natural_left`,
  `CategoryTheory.Adjunction.leftProjectionMorphism_natural_right`: naturality of the left
  projection morphism.
- `CategoryTheory.Adjunction.derivedLeftProjectionMorphism_Qh_obj`: the derived left projection
  morphism on the image of complexes.
- `CategoryTheory.Adjunction.isIso_derivedLeftProjectionMorphism_Qh_obj`: the derived left
  projection morphism at the image of a complex `Z` is an isomorphism if the left projection
  morphisms of `F ⊣ G` at the components of `Z` are.
-/

@[expose] public section

universe u u₁ u₂

open CategoryTheory MonoidalCategory Limits

namespace CochainComplex.Monoidal

variable {C : Type*} [Category* C] [Preadditive C] [MonoidalCategory C] [HasZeroObject C]
  [MonoidalPreadditive C]
  [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

/-- On the summand `K.X p ⊗ L.X q`, left whiskering by `g : L ⟶ L'` is `K.X p ◁ g.f q`. -/
@[reassoc]
lemma ι_whiskerLeft (K : CochainComplex C ℤ) {L L' : CochainComplex C ℤ} (g : L ⟶ L')
    (p q n : ℤ) (h : p + q = n) :
    HomologicalComplex.ιTensorObj K L p q n h ≫ (K ◁ g).f n =
      (K.X p ◁ g.f q) ≫ HomologicalComplex.ιTensorObj K L' p q n h := by
  erw [HomologicalComplex.ι_mapBifunctorMap]
  simp

end CochainComplex.Monoidal

namespace CategoryTheory.Adjunction

section Naturality

open Functor.OplaxMonoidal

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G) [F.OplaxMonoidal]

/-- The left projection morphism `B ⊗ G A ⟶ G (F B ⊗ A)` is natural in `B`. -/
@[reassoc]
lemma leftProjectionMorphism_natural_left {B B' : D} (h : B ⟶ B') (A : C) :
    h ▷ G.obj A ≫ adj.leftProjectionMorphism B' A =
      adj.leftProjectionMorphism B A ≫ G.map (F.map h ▷ A) := by
  rw [leftProjectionMorphism, leftProjectionMorphism, ← homEquiv_naturality_left,
    ← homEquiv_naturality_right, ← δ_natural_left_assoc, Category.assoc, whisker_exchange]

/-- The left projection morphism `B ⊗ G A ⟶ G (F B ⊗ A)` is natural in `A`. -/
@[reassoc]
lemma leftProjectionMorphism_natural_right (B : D) {A A' : C} (h : A ⟶ A') :
    B ◁ G.map h ≫ adj.leftProjectionMorphism B A' =
      adj.leftProjectionMorphism B A ≫ G.map (F.obj B ◁ h) := by
  rw [leftProjectionMorphism, leftProjectionMorphism, ← homEquiv_naturality_left,
    ← homEquiv_naturality_right, ← δ_natural_right_assoc, Category.assoc,
    ← MonoidalCategory.whiskerLeft_comp, ← MonoidalCategory.whiskerLeft_comp,
    adj.counit_naturality]

/-- The invertibility of a left projection morphism only depends on its first argument up to
isomorphism. -/
lemma isIso_leftProjectionMorphism_iff_of_iso_left {B B' : D} (e : B ≅ B') (A : C) :
    IsIso (adj.leftProjectionMorphism B A) ↔ IsIso (adj.leftProjectionMorphism B' A) := by
  have h := adj.leftProjectionMorphism_natural_left e.hom A
  constructor
  · intro
    rw [← isIso_comp_left_iff (e.hom ▷ G.obj A), h]
    infer_instance
  · intro
    rw [← isIso_comp_right_iff _ (G.map (F.map e.hom ▷ A)), ← h]
    infer_instance

/-- The invertibility of a left projection morphism only depends on its second argument up to
isomorphism. -/
lemma isIso_leftProjectionMorphism_iff_of_iso_right (B : D) {A A' : C} (e : A ≅ A') :
    IsIso (adj.leftProjectionMorphism B A) ↔ IsIso (adj.leftProjectionMorphism B A') := by
  have h := adj.leftProjectionMorphism_natural_right B e.hom
  constructor
  · intro
    rw [← isIso_comp_left_iff (B ◁ G.map e.hom), h]
    infer_instance
  · intro
    rw [← isIso_comp_right_iff _ (G.map (F.obj B ◁ e.hom)), ← h]
    infer_instance

end Naturality

end CategoryTheory.Adjunction

namespace CategoryTheory.Adjunction

section Complexes

open Functor.OplaxMonoidal

variable {C : Type u₁} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  {D : Type u₂} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.Additive] [G.Additive] [F.Monoidal]
  [F.IsLeftAdjoint]

/-- The left projection morphism of the adjunction induced on complexes, on the summand
`P^p ⊗ G Z^q`, is the left projection morphism of `F ⊣ G` in degrees `(p, q)`. -/
lemma ιTensorObj_mapHomologicalComplex_leftProjectionMorphism_f (P : CochainComplex C ℤ)
    (Z : CochainComplex D ℤ) (p q n : ℤ) (h : p + q = n) :
    HomologicalComplex.ιTensorObj P ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj Z)
        p q n h ≫
      ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).leftProjectionMorphism P Z).f n =
    adj.leftProjectionMorphism (P.X p) (Z.X q) ≫ G.map (HomologicalComplex.ιTensorObj
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) Z p q n h) := by
  have hu := adj.unit.naturality
    (HomologicalComplex.ιTensorObj P ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj Z)
      p q n h)
  have hδ := HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX
    (Functor.OplaxMonoidal.δNatTrans F) (ComplexShape.up ℤ)
    P ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj Z) p q n h
  have hw := CochainComplex.Monoidal.ι_whiskerLeft
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
    ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app Z) p q n h
  rw [Adjunction.leftProjectionMorphism, Adjunction.leftProjectionMorphism,
    Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f, HomologicalComplex.comp_f,
    Functor.map_comp]
  erw [reassoc_of% hu]
  simp only [Category.assoc, ← Functor.map_comp]
  congr 2
  erw [reassoc_of% hδ, hw]
  rfl

variable [G.IsLeftAdjoint] in
/-- The left projection morphism of the adjunction induced on complexes is an isomorphism at
`(P, Z)` if the left projection morphisms of `F ⊣ G` at the components of `P` and `Z` are. -/
lemma isIso_mapHomologicalComplex_leftProjectionMorphism (P : CochainComplex C ℤ)
    (Z : CochainComplex D ℤ) (hPZ : ∀ p q, IsIso (adj.leftProjectionMorphism (P.X p) (Z.X q))) :
    IsIso ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).leftProjectionMorphism P Z) := by
  have (n : ℤ) : IsIso (((adj.mapHomologicalComplex
      (ComplexShape.up ℤ)).leftProjectionMorphism P Z).f n) :=
    isIso_of_isColimit_cofan
      (HomologicalComplex.mapBifunctor.isColimitMapCofan (G := 𝟭 _) _ _ n)
      (HomologicalComplex.mapBifunctor.isColimitMapCofan (G := G) _ _ n) _
      (fun x ↦ adj.leftProjectionMorphism (P.X x.1.1) (Z.X x.1.2))
      (fun x ↦ ιTensorObj_mapHomologicalComplex_leftProjectionMorphism_f adj P Z _ _ n x.2)
  exact HomologicalComplex.Hom.isIso_of_components _

/-- The left projection morphism of the adjunction induced on homotopy categories, on the image
of complexes, is the image of the left projection morphism of the adjunction induced on
complexes. -/
lemma mapHomotopyCategory_leftProjectionMorphism_quotient (P : CochainComplex C ℤ)
    (Z : CochainComplex D ℤ) :
    (adj.mapHomotopyCategory (ComplexShape.up ℤ)).leftProjectionMorphism
        ((HomotopyCategory.quotient _ _).obj P) ((HomotopyCategory.quotient _ _).obj Z) =
      (HomotopyCategory.quotient _ _).map ((adj.mapHomologicalComplex
        (ComplexShape.up ℤ)).leftProjectionMorphism P Z) := by
  rw [Adjunction.leftProjectionMorphism, Adjunction.leftProjectionMorphism,
    Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp]
  erw [Adjunction.mapHomotopyCategory_unit_app_quotient]
  erw [Adjunction.mapHomotopyCategory_counit_app_quotient,
    ← HomotopyCategory.MonoidalCategory.quotient_map_whiskerLeft']
  rw [Functor.map_comp, Functor.map_comp, Functor.map_comp, Functor.mapHomotopyCategory_δ]
  erw [Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans_app_app,
    Functor.mapHomotopyCategory_map, Functor.mapHomotopyCategory_map]
  rfl

end Complexes

end CategoryTheory.Adjunction

namespace CategoryTheory.Adjunction

section Derived

open Functor.LaxMonoidal Functor.OplaxMonoidal DerivedCategory

variable {C : Type u₁} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]
  {D : Type u₂} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [Abelian.HasFunctorialFlatResolution D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.Additive] [G.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [F.PreservesKFlatQuasiIso] [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal]
  (adjD : F.leftDerivedFunctor ⊣ G.mapDerivedCategory)

/-- **The derived left projection morphism on the image of complexes.** Let
`adjD : LF ⊣ D(G)` be an adjunction whose counit (`hε`) and unit (`hη`) are computed on the
image of complexes by those of `F ⊣ G`. Then the left projection morphism
`Qh P ⊗ᴸ D(G) (Qh Z) ⟶ D(G) (LF (Qh P) ⊗ᴸ Qh Z)` of `adjD` is, modulo the comparison maps, the
image of the left projection morphism of the adjunction induced on homotopy categories. -/
lemma derivedLeftProjectionMorphism_Qh_obj
    (hε : ∀ Z : HomotopyCategory D (.up ℤ), adjD.counit.app (Qh.obj Z) =
      F.leftDerivedFunctor.map (G.mapDerivedCategoryFactorsh.hom.app Z) ≫
        F.leftDerivedFunctorCounit.app ((G.mapHomotopyCategory (.up ℤ)).obj Z) ≫
        Qh.map ((adj.mapHomotopyCategory (.up ℤ)).counit.app Z))
    (hη : ∀ K : HomotopyCategory C (.up ℤ), adjD.unit.app (Qh.obj K) ≫
      G.mapDerivedCategory.map (F.leftDerivedFunctorCounit.app K) ≫
        G.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj K) =
      Qh.map ((adj.mapHomotopyCategory (.up ℤ)).unit.app K))
    (P : HomotopyCategory C (.up ℤ)) (Z : HomotopyCategory D (.up ℤ)) :
    letI := F.leftDerivedFunctorMonoidal
    (Qh.obj P ◁ G.mapDerivedCategoryFactorsh.inv.app Z) ≫
      adjD.leftProjectionMorphism (Qh.obj P) (Qh.obj Z) ≫
      G.mapDerivedCategory.map (F.leftDerivedFunctorCounit.app P ▷ Qh.obj Z ≫
        μ Qh ((F.mapHomotopyCategory (.up ℤ)).obj P) Z) ≫
      G.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj P ⊗ Z) =
    μ Qh P ((G.mapHomotopyCategory (.up ℤ)).obj Z) ≫
      Qh.map ((adj.mapHomotopyCategory (.up ℤ)).leftProjectionMorphism P Z) := by
  let := F.leftDerivedFunctorMonoidal
  have hinner : F.leftDerivedFunctor.map (Qh.obj P ◁ G.mapDerivedCategoryFactorsh.inv.app Z) ≫
      δ F.leftDerivedFunctor _ _ ≫
      F.leftDerivedFunctor.obj (Qh.obj P) ◁ adjD.counit.app (Qh.obj Z) ≫
      F.leftDerivedFunctorCounit.app P ▷ Qh.obj Z ≫
      μ Qh ((F.mapHomotopyCategory (.up ℤ)).obj P) Z =
    F.leftDerivedFunctor.map (μ Qh P ((G.mapHomotopyCategory (.up ℤ)).obj Z)) ≫
      F.leftDerivedFunctorCounit.app _ ≫
      Qh.map (δ (F.mapHomotopyCategory (.up ℤ)) P ((G.mapHomotopyCategory (.up ℤ)).obj Z) ≫
        (F.mapHomotopyCategory (.up ℤ)).obj P ◁
          (adj.mapHomotopyCategory (.up ℤ)).counit.app Z) := by
    have h4 := F.leftDerivedTensorComparison_app_app_comp_tensorHom P
      ((G.mapHomotopyCategory (.up ℤ)).obj Z)
    rw [← δ_natural_right_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, hε,
      ← Functor.map_comp_assoc, Iso.inv_hom_id_app, Functor.map_id, Category.id_comp,
      MonoidalCategory.whiskerLeft_comp_assoc]
    erw [whisker_exchange_assoc]
    have hμ := μ_natural_right Qh ((F.mapHomotopyCategory (.up ℤ)).obj P)
      ((adj.mapHomotopyCategory (.up ℤ)).counit.app Z)
    erw [hμ]
    rw [← tensorHom_def'_assoc]
    erw [reassoc_of% h4]
    rw [Functor.map_comp]
    rfl
  have hη₁ := adjD.unit.naturality (Qh.obj P ◁ G.mapDerivedCategoryFactorsh.inv.app Z)
  have hη₂ := adjD.unit.naturality (μ Qh P ((G.mapHomotopyCategory (.up ℤ)).obj Z))
  have hi := G.mapDerivedCategoryFactorsh.hom.naturality
    (δ (F.mapHomotopyCategory (.up ℤ)) P ((G.mapHomotopyCategory (.up ℤ)).obj Z) ≫
      (F.mapHomotopyCategory (.up ℤ)).obj P ◁ (adj.mapHomotopyCategory (.up ℤ)).counit.app Z)
  have hu := hη (P ⊗ (G.mapHomotopyCategory (.up ℤ)).obj Z)
  dsimp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map] at hη₁ hη₂ hi
  rw [leftProjectionMorphism, leftProjectionMorphism, homEquiv_unit, homEquiv_unit,
    Category.assoc, reassoc_of% hη₁, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  simp only [Category.assoc]
  erw [hinner]
  rw [Functor.map_comp, Category.assoc, ← reassoc_of% hη₂, Functor.map_comp, Category.assoc,
    hi, reassoc_of% hu, Functor.map_comp]
  simp only [Functor.map_comp]
/-- **The derived left projection morphism is an isomorphism at the image of a complex.** Let
`adjD : LF ⊣ D(G)` be an adjunction whose counit (`hε`) and unit (`hη`) are computed on the
image of complexes by those of `F ⊣ G`, with `G` preserving colimits, and let `Z` be a complex
such that the left projection morphisms `B ⊗ G Z^q ⟶ G (F B ⊗ Z^q)` of `F ⊣ G` are
isomorphisms. Then the left projection morphisms `K ⊗ᴸ D(G) (Qh Z) ⟶ D(G) (LF K ⊗ᴸ Qh Z)` of
`adjD` are isomorphisms. -/
theorem isIso_derivedLeftProjectionMorphism_Qh_obj [G.IsLeftAdjoint]
    (hε : ∀ Z : HomotopyCategory D (.up ℤ), adjD.counit.app (Qh.obj Z) =
      F.leftDerivedFunctor.map (G.mapDerivedCategoryFactorsh.hom.app Z) ≫
        F.leftDerivedFunctorCounit.app ((G.mapHomotopyCategory (.up ℤ)).obj Z) ≫
        Qh.map ((adj.mapHomotopyCategory (.up ℤ)).counit.app Z))
    (hη : ∀ K : HomotopyCategory C (.up ℤ), adjD.unit.app (Qh.obj K) ≫
      G.mapDerivedCategory.map (F.leftDerivedFunctorCounit.app K) ≫
        G.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj K) =
      Qh.map ((adj.mapHomotopyCategory (.up ℤ)).unit.app K))
    (Z : CochainComplex D ℤ) (hZ : ∀ (B : C) (q : ℤ), IsIso (adj.leftProjectionMorphism B (Z.X q)))
    (K : DerivedCategory C) :
    letI := F.leftDerivedFunctorMonoidal
    IsIso (adjD.leftProjectionMorphism K (Qh.obj ((HomotopyCategory.quotient _ _).obj Z))) := by
  let := F.leftDerivedFunctorMonoidal
  obtain ⟨P, hP, ⟨e⟩⟩ := F.exists_kFlatKFlatMap_iso K
  rw [← isIso_leftProjectionMorphism_iff_of_iso_left _ e]
  obtain ⟨P', rfl⟩ := HomotopyCategory.quotient_obj_surjective P
  have h := derivedLeftProjectionMorphism_Qh_obj adj adjD hε hη
    ((HomotopyCategory.quotient _ _).obj P') ((HomotopyCategory.quotient _ _).obj Z)
  rw [mapHomotopyCategory_leftProjectionMorphism_quotient] at h
  have := isIso_mapHomologicalComplex_leftProjectionMorphism adj P' Z (fun _ q ↦ hZ _ q)
  have := F.isIso_leftDerivedFunctorCounit_app_of_kFlat' _ hP.1
  have := DerivedCategory.isIso_μ_Qh_of_kFlat _
    ((G.mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj Z)) hP.1
  have := DerivedCategory.isIso_μ_Qh_of_kFlat
    ((F.mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj P'))
    ((HomotopyCategory.quotient _ _).obj Z) hP.2
  have hd : IsIso (μ Qh ((HomotopyCategory.quotient _ _).obj P')
      ((G.mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj Z)) ≫
      Qh.map ((HomotopyCategory.quotient _ _).map ((adj.mapHomologicalComplex
        (ComplexShape.up ℤ)).leftProjectionMorphism P' Z))) := inferInstance
  rw [← h, isIso_comp_left_iff, isIso_comp_right_iff] at hd
  exact hd

end Derived

end CategoryTheory.Adjunction
