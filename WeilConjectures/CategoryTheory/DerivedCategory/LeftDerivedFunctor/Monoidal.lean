/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.HomotopyCategory.DerivabilityStructure
public import WeilConjectures.Algebra.Homology.HomotopyCategory.OplaxMonoidal
public import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.DerivesTwo
public import WeilConjectures.Mathlib.CategoryTheory.Whiskering

/-!
# The tensor comparison of the left derived functor of an exact monoidal functor

Let `F : C ⥤ D` be an exact strong monoidal functor between monoidal Grothendieck abelian
categories with functorial flat resolutions, which preserves flat objects and `ℤ`-indexed
colimits. We show that the bifunctors `(K, M) ↦ LF(K ⊗ᴸ M)` and `(K, M) ↦ LF K ⊗ᴸ LF M` are the
total left derived functors of `(A, B) ↦ F(A ⊗ B)` and `(A, B) ↦ F A ⊗ F B`, and derive the
comonoidal structure `δ` of `F` into a natural isomorphism
`LF(K ⊗ᴸ M) ≅ LF K ⊗ᴸ LF M`.

This is the common generalisation of the tensor comparisons of the derived pullbacks
`AlgebraicGeometry.Etale.leftDerivedUpperStarTensorComparison` and
`AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorComparison`, which are its instances, and
it applies as well to the comparison functor between étale and pro-étale sheaves.

We then show that this comparison is compatible with the composition of functors and with
monoidal natural isomorphisms.

## Main definitions and results

- `CategoryTheory.Functor.kFlatMap F`: the complexes whose image under `F` is K-flat; they
  form a left derivability structure.
- `CategoryTheory.Functor.leftDerivedTensorComparison F`: the comparison
  `LF(K ⊗ᴸ M) ⟶ LF K ⊗ᴸ LF M`, an isomorphism.
- `CategoryTheory.Functor.leftDerivedTensorComparison_comp`: the comparison of `F ⋙ G` is the
  comparison of `F` followed by the comparison of `G`.
- `CategoryTheory.Functor.leftDerivedTensorComparison_of_iso`: a monoidal natural isomorphism
  `F ≅ F'` carries the comparison of `F` to the one of `F'`.
-/

@[expose] public section

universe u u₁ u₂ u₃

open CategoryTheory Abelian Limits MonoidalCategory DerivedCategory

open scoped CategoryTheory.Functor

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [SymmetricCategory C]
  [HasFunctorialFlatResolution C]
  {D : Type u₂} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [SymmetricCategory D]
  [HasFunctorialFlatResolution D]

section

variable (F : C ⥤ D) [F.Additive]

/-- The complexes in `K(C)` whose image under `F : C ⥤ D` is K-flat: the inverse image of the
K-flat complexes of `K(D)` under `K(F) : K(C) ⥤ K(D)`. -/
abbrev kFlatMap : ObjectProperty (HomotopyCategory C (.up ℤ)) :=
  (HomotopyCategory.quasiIso D (.up ℤ)).kFlat.inverseImage (F.mapHomotopyCategory (.up ℤ))

variable [F.PreservesFlat] [PreservesColimitsOfShape ℤ F]

/-- A functor preserving flat objects and `ℤ`-indexed colimits sends the functorial flat
resolutions to K-flat complexes. -/
lemma kFlatMap_quotient_obj_resolutionFunctor_obj
    (Λ : LeftResolution (ObjectProperty.flat.ι : _ ⥤ C)) [Λ.F.PreservesZeroMorphisms]
    (K : CochainComplex C ℤ) :
    F.kFlatMap ((HomotopyCategory.quotient _ _).obj (Λ.resolutionFunctor.obj K)) :=
  ObjectProperty.prop_of_iso (HomotopyCategory.quasiIso D (.up ℤ)).kFlat
    ((F.mapHomotopyCategoryFactors (.up ℤ)).app (Λ.resolutionFunctor.obj K)).symm
    ((HomotopyCategory.kFlat_quotient_obj_iff _).2
      (F.kFlat_mapHomologicalComplex_obj_resolutionFunctor_obj Λ
        ObjectProperty.flat.essImage_ι_le K))

/-- The complexes whose image under `F` is K-flat form a left derivability structure on
`K(C)` for the quasi-isomorphisms. -/
instance isLeftDerivabilityStructure_kFlatMap :
    (HomotopyCategory.quasiIsoLocalizerMorphism F.kFlatMap).IsLeftDerivabilityStructure :=
  let Λ := (inferInstance : HasFunctorialFlatResolution C).some
  HomotopyCategory.isLeftDerivabilityStructure_quasiIsoLocalizerMorphism _
    Λ.reduced.resolutionNatTrans (fun _ ↦ inferInstance)
    (F.kFlatMap_quotient_obj_resolutionFunctor_obj Λ.reduced)

end
/-- The lax monoidal structure `Qh K ⊗ᴸ Qh M ⟶ Qh (K ⊗ M)` of `Qh : K(C) ⥤ D(C)` is an
isomorphism when `M` is K-flat. -/
lemma isIso_μNatTrans_Qh_app_app_of_kFlat (K M : HomotopyCategory C (.up ℤ))
    (hM : (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat M) :
    IsIso (((LaxMonoidal.μNatTrans (Qh (C := C))).app K).app M) :=
  have := DerivedCategory.isLeftDerivedFunctor₂CurriedTensor C
  (MorphismProperty.id_prod_kFlat_derives_curriedTensor
    (HomotopyCategory.quasiIso C (.up ℤ)) Qh).isIso_of_isLeftDerivabilityStructure
      (LF := curriedTensor (DerivedCategory C)) (LaxMonoidal.μNatTrans Qh) K ⟨_, hM⟩

section Comparison

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The bifunctor `(K, M) ↦ LF K ⊗ᴸ LF M`, of type `D(C) ⥤ D(C) ⥤ D(D)`. -/
noncomputable abbrev derivedTensorLeftDerived :
    DerivedCategory C ⥤ DerivedCategory C ⥤ DerivedCategory D :=
  (((whiskeringLeft₂ _).obj F.leftDerivedFunctor).obj F.leftDerivedFunctor).obj
    (curriedTensor _)

/-- The bifunctor `(K, M) ↦ LF(K ⊗ᴸ M)`, of type `D(C) ⥤ D(C) ⥤ D(D)`. -/
noncomputable abbrev leftDerivedDerivedTensor :
    DerivedCategory C ⥤ DerivedCategory C ⥤ DerivedCategory D :=
  (postcompose₂.obj F.leftDerivedFunctor).obj (curriedTensor _)

/-- The counit exhibiting `(K, M) ↦ LF K ⊗ᴸ LF M` as the total left derived functor of
`(A, B) ↦ F A ⊗ F B`. On `K, M` in `K(C)` it is the composite
```
 LF(Qh K) ⊗ᴸ LF(Qh M) --(counit ⊗ᴸ 1)--> Qh(F K) ⊗ᴸ LF(Qh M)
   --(1 ⊗ᴸ counit)--> Qh(F K) ⊗ᴸ Qh(F M) --(μ Qh)--> Qh(F K ⊗ F M)
```
of the counits of `LF` on both factors and the lax monoidal structure of
`Qh : K(D) ⥤ D(D)`. -/
noncomputable def derivedTensorLeftDerivedCounit :
    (((whiskeringLeft₂ _).obj (Qh (C := C))).obj Qh).obj (derivedTensorLeftDerived F) ⟶
      (((whiskeringLeft₂ _).obj (F.mapHomotopyCategory (.up ℤ))).obj
        (F.mapHomotopyCategory (.up ℤ))).obj
          ((postcompose₂.obj Qh).obj (curriedTensor _)) :=
  (((whiskeringLeft₂ _).map F.leftDerivedFunctorCounit).app
      (Qh ⋙ F.leftDerivedFunctor)).app (curriedTensor _) ≫
    (((whiskeringLeft₂ _).obj (F.mapHomotopyCategory (.up ℤ) ⋙ Qh)).map
      F.leftDerivedFunctorCounit).app (curriedTensor _) ≫
    (((whiskeringLeft₂ _).obj (F.mapHomotopyCategory (.up ℤ))).obj
        (F.mapHomotopyCategory (.up ℤ))).map (LaxMonoidal.μNatTrans Qh)

/-- The counit exhibiting `(K, M) ↦ LF(K ⊗ᴸ M)` as the total left derived functor of
`(A, B) ↦ F(A ⊗ B)`. On `K, M` in `K(C)` it is the composite
```
 LF(Qh K ⊗ᴸ Qh M) --(LF(μ Qh))--> LF(Qh (K ⊗ M)) --(counit)--> Qh(F(K ⊗ M))
```
-/
noncomputable def leftDerivedDerivedTensorCounit :
    (((whiskeringLeft₂ _).obj (Qh (C := C))).obj Qh).obj (leftDerivedDerivedTensor F) ⟶
      (postcompose₂.obj (F.mapHomotopyCategory (.up ℤ) ⋙ Qh)).obj (curriedTensor _) :=
  (postcompose₂.obj F.leftDerivedFunctor).map (LaxMonoidal.μNatTrans Qh) ≫
    (postcompose₂.map F.leftDerivedFunctorCounit).app (curriedTensor _)

variable [F.PreservesFlat] [F.IsLeftAdjoint]

/-- `(K, M) ↦ LF K ⊗ᴸ LF M` is the total left derived functor of `(A, B) ↦ F A ⊗ F B`. It is
computed on pairs `(K, M)` with `K` K-flat and `F M` K-flat. -/
instance isLeftDerivedFunctor₂_derivedTensorLeftDerived :
    (derivedTensorLeftDerived F).IsLeftDerivedFunctor₂ (derivedTensorLeftDerivedCounit F)
      (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) := by
  refine LocalizerMorphism.isLeftDerivedFunctor₂_of_isLeftDerivabilityStructure
    (HomotopyCategory.quasiIso _ (.up ℤ)).localizerMorphismKFlat
    (HomotopyCategory.quasiIsoLocalizerMorphism F.kFlatMap) _ (fun X₁ X₂ ↦ ?_)
  have := isIso_μNatTrans_Qh_app_app_of_kFlat
    ((F.mapHomotopyCategory _).obj X₁.obj) _ X₂.property
  simp only [derivedTensorLeftDerivedCounit, NatTrans.comp_app]
  exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' inferInstance this)

/-- `(K, M) ↦ LF(K ⊗ᴸ M)` is the total left derived functor of `(A, B) ↦ F(A ⊗ B)`. It is
computed on pairs of K-flat complexes. -/
instance isLeftDerivedFunctor₂_leftDerivedDerivedTensor :
    (leftDerivedDerivedTensor F).IsLeftDerivedFunctor₂ (leftDerivedDerivedTensorCounit F)
      (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) := by
  refine LocalizerMorphism.isLeftDerivedFunctor₂_of_isLeftDerivabilityStructure
    (HomotopyCategory.quasiIso _ (.up ℤ)).localizerMorphismKFlat
    (HomotopyCategory.quasiIso _ (.up ℤ)).localizerMorphismKFlat _ (fun X₁ X₂ ↦ ?_)
  have := isIso_μNatTrans_Qh_app_app_of_kFlat X₁.obj _ X₂.property
  simp only [leftDerivedDerivedTensorCounit, NatTrans.comp_app]
  exact IsIso.comp_isIso'
    (Functor.map_isIso F.leftDerivedFunctor (((LaxMonoidal.μNatTrans Qh).app X₁.obj).app X₂.obj))
    inferInstance

variable [F.Monoidal]

/-- The comparison `LF(K ⊗ᴸ M) ⟶ LF K ⊗ᴸ LF M` of bifunctors `D(C) ⥤ D(C) ⥤ D(D)`, obtained by
deriving the comonoidal structure `δ` of `F`. It is the unique natural transformation such
that, for `K, M` in `K(C)`, the square
```
  LF(Qh K ⊗ᴸ Qh M) ──comparison──▶ LF(Qh K) ⊗ᴸ LF(Qh M)
          │                                │
          ▼                                ▼
     Qh(F(K ⊗ M)) ──────Qh(δ F)─────▶ Qh(F K ⊗ F M)
```
commutes, the vertical arrows being `leftDerivedDerivedTensorCounit` and
`derivedTensorLeftDerivedCounit`. -/
noncomputable def leftDerivedTensorComparison :
    leftDerivedDerivedTensor F ⟶ derivedTensorLeftDerived F :=
  leftDerived₂NatTrans _ (derivedTensorLeftDerivedCounit F)
    (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) _
    (leftDerivedDerivedTensorCounit F)
    (postcompose₂MapWhiskeringLeft₂ (OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) F) Qh)

/-- The characterising property of `leftDerivedTensorComparison`. -/
@[reassoc]
lemma leftDerivedTensorComparison_app_app_comp_counit (K M : HomotopyCategory C (.up ℤ)) :
    ((F.leftDerivedTensorComparison.app (Qh.obj K)).app (Qh.obj M)) ≫
        ((derivedTensorLeftDerivedCounit F).app K).app M =
      ((leftDerivedDerivedTensorCounit F).app K).app M ≫
        Qh.map (((OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) F).app K).app M) :=
  leftDerived₂NatTrans_app_app _ _ _ _ _ _ _ K M

/-- The comparison `LF(K ⊗ᴸ M) ⟶ LF K ⊗ᴸ LF M` is an isomorphism, `F` being strong monoidal. -/
instance isIso_leftDerivedTensorComparison : IsIso F.leftDerivedTensorComparison := by
  dsimp only [leftDerivedTensorComparison]
  infer_instance

end Comparison
section ComplexLevel

open OplaxMonoidal LaxMonoidal

variable {E : Type u₃} [Category.{u + 1} E] [Abelian E] [IsGrothendieckAbelian.{u + 1} E]
  [MonoidalCategory E] [MonoidalPreadditive E] [MonoidalClosed E] [SymmetricCategory E]
  [HasFunctorialFlatResolution E]

open HomologicalComplex in
/-- The comonoidal comparison `(F ⋙ G)(K ⊗ L) ⟶ (F ⋙ G) K ⊗ (F ⋙ G) L` of complexes is the
comparison of `F` followed by the comparison of `G`. -/
lemma mapHomologicalComplexδNatTrans_comp (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [F.IsLeftAdjoint] [G.IsLeftAdjoint] [F.OplaxMonoidal] [G.OplaxMonoidal]
    (K L : CochainComplex C ℤ) :
    ((OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) (F ⋙ G)).app K).app L =
      (G.mapHomologicalComplex _).map
          (((OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app K).app L) ≫
        ((OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) G).app
          ((F.mapHomologicalComplex _).obj K)).app ((F.mapHomologicalComplex _).obj L) := by
  ext n
  refine mapBifunctor.hom_ext_of_map (F ⋙ G) (fun i₁ i₂ h ↦ ?_)
  simp only [OplaxMonoidal.mapHomologicalComplexδNatTrans_app_app, mapBifunctorComparison_f,
    comp_f, Functor.mapHomologicalComplex_map_f, map_ιMapBifunctor_mapBifunctorComparisonX]
  erw [Functor.comp_map, ← G.map_comp_assoc, map_ιMapBifunctor_mapBifunctorComparisonX,
    G.map_comp_assoc, map_ιMapBifunctor_mapBifunctorComparisonX]
  simp
  rfl

open HomologicalComplex in
/-- A monoidal natural transformation `τ : F ⟶ F'` commutes with the comonoidal comparisons
of complexes. -/
lemma mapHomologicalComplexδNatTrans_naturality {F F' : C ⥤ D} [F.Additive] [F'.Additive]
    [F.IsLeftAdjoint] [F'.IsLeftAdjoint] [F.Monoidal] [F'.Monoidal] (τ : F ⟶ F')
    [NatTrans.IsMonoidal τ] (K L : CochainComplex C ℤ) :
    (NatTrans.mapHomologicalComplex τ (.up ℤ)).app (K ⊗ L) ≫
        ((OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F').app K).app L =
      ((OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app K).app L ≫
        ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app K ⊗ₘ
          (NatTrans.mapHomologicalComplex τ (.up ℤ)).app L) := by
  ext n
  refine mapBifunctor.hom_ext_of_map F (fun i₁ i₂ h ↦ ?_)
  have hτ : δ F (K.X i₁) (L.X i₂) ≫ (τ.app (K.X i₁) ⊗ₘ τ.app (L.X i₂)) =
      τ.app _ ≫ δ F' (K.X i₁) (L.X i₂) := by
    rw [← cancel_epi (μ F (K.X i₁) (L.X i₂)), Monoidal.μ_δ_assoc,
      NatTrans.IsMonoidal.tensor_assoc, Monoidal.μ_δ, Category.comp_id]
  rw [comp_f, comp_f, NatTrans.mapHomologicalComplex_app_f]
  have hn := τ.naturality (ιMapBifunctor K L (curriedTensor C) (.up ℤ) i₁ i₂ n h)
  erw [reassoc_of% hn, map_ιMapBifunctor_mapBifunctorComparisonX,
    map_ιMapBifunctor_mapBifunctorComparisonX_assoc]
  erw [ι_mapBifunctorMap]
  simp only [mapBifunctorComparisonApp, OplaxMonoidal.δNatTrans_app_app]
  erw [← reassoc_of% hτ]
  simp [tensorHom_def]
  rfl

end ComplexLevel
section Compatibility

open OplaxMonoidal LaxMonoidal

variable {E : Type u₃} [Category.{u + 1} E] [Abelian E] [IsGrothendieckAbelian.{u + 1} E]
  [MonoidalCategory E] [MonoidalPreadditive E] [MonoidalClosed E] [SymmetricCategory E]
  [HasFunctorialFlatResolution E]

/-- The composition isomorphism `L(F ⋙ G) ≅ LF ⋙ LG` is compatible with the counits. -/
@[reassoc]
lemma leftDerivedFunctorCompIso_hom_app_comp_counit (F : C ⥤ D) (G : D ⥤ E) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (X : HomotopyCategory C (.up ℤ)) :
    (F.leftDerivedFunctorCompIso G).hom.app (Qh.obj X) ≫
        G.leftDerivedFunctor.map (F.leftDerivedFunctorCounit.app X) ≫
        G.leftDerivedFunctorCounit.app ((F.mapHomotopyCategory _).obj X) =
      (F ⋙ G).leftDerivedFunctorCounit.app X := by
  have h₁ := congr_app (F ⋙ G).leftDerivedFunctorIsoMapDerivedCategory_hom_fac X
  have h₂ := congr_app F.leftDerivedFunctorIsoMapDerivedCategory_hom_fac X
  have h₃ := congr_app G.leftDerivedFunctorIsoMapDerivedCategory_hom_fac
    ((F.mapHomotopyCategory _).obj X)
  have h₄ := mapDerivedCategoryCompIso_fach F G X
  rw [mapHomotopyCategoryCompIso_refl_hom_app] at h₄
  erw [Qh.map_id, Category.comp_id] at h₄
  dsimp at h₁ h₂ h₃ h₄
  simp only [leftDerivedFunctorCompIso, Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom,
    isoWhiskerLeft_hom, Iso.symm_hom, whiskerRight_app, whiskerLeft_app, Category.assoc]
  rw [← h₁, ← h₄, ← h₂, ← h₃]
  simp only [← Category.assoc]
  congr 1
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app_assoc]
  rw [← (G.leftDerivedFunctorIsoMapDerivedCategory.inv.naturality_assoc)]
  simp

/-- An isomorphism `F ≅ F'` of exact functors is compatible with the counits of their total
left derived functors. -/
@[reassoc]
lemma leftDerivedFunctorNatIso_hom_app_comp_counit {F F' : C ⥤ D} [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F'.Additive]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F'] (τ : F ≅ F')
    (X : HomotopyCategory C (.up ℤ)) :
    (F.leftDerivedFunctorNatIso τ).hom.app (Qh.obj X) ≫ F'.leftDerivedFunctorCounit.app X =
      F.leftDerivedFunctorCounit.app X ≫
        Qh.map ((NatTrans.mapHomotopyCategory τ.hom (.up ℤ)).app X) := by
  have h₁ := congr_app F.leftDerivedFunctorIsoMapDerivedCategory_hom_fac X
  have h₂ := congr_app F'.leftDerivedFunctorIsoMapDerivedCategory_hom_fac X
  have h₃ := mapDerivedCategoryNatIso_fach τ X
  dsimp at h₁ h₂ h₃
  simp only [leftDerivedFunctorNatIso, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
    Category.assoc]
  rw [← h₁, ← h₂, Iso.inv_hom_id_app_assoc, h₃, Category.assoc]
open HomotopyCategory in
/-- A monoidal natural transformation `τ : F ⟶ F'` commutes with the comonoidal comparisons
in the homotopy category. -/
lemma mapHomotopyCategoryδNatTrans_naturality {F F' : C ⥤ D} [F.Additive] [F'.Additive]
    [F.IsLeftAdjoint] [F'.IsLeftAdjoint] [F.Monoidal] [F'.Monoidal] (τ : F ⟶ F')
    [NatTrans.IsMonoidal τ] (X₁ X₂ : HomotopyCategory C (.up ℤ)) :
    (NatTrans.mapHomotopyCategory τ (.up ℤ)).app (X₁ ⊗ X₂) ≫
        ((mapHomotopyCategoryδNatTrans (.up ℤ) F').app X₁).app X₂ =
      ((mapHomotopyCategoryδNatTrans (.up ℤ) F).app X₁).app X₂ ≫
        ((NatTrans.mapHomotopyCategory τ (.up ℤ)).app X₁ ⊗ₘ
          (NatTrans.mapHomotopyCategory τ (.up ℤ)).app X₂) := by
  obtain ⟨K, rfl⟩ := quotient_obj_surjective X₁
  obtain ⟨L, rfl⟩ := quotient_obj_surjective X₂
  have h := (quotient D (.up ℤ)).congr_map (mapHomologicalComplexδNatTrans_naturality τ K L)
  have hq : (quotient D (.up ℤ)).map ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app K ⊗ₘ
      (NatTrans.mapHomologicalComplex τ (.up ℤ)).app L) =
      (quotient D (.up ℤ)).map ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app K) ⊗ₘ
        (quotient D (.up ℤ)).map ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app L) := by
    rw [Functor.Monoidal.map_tensor]
    exact (Category.id_comp _).trans (Category.comp_id _)
  rw [Functor.map_comp, Functor.map_comp, hq] at h
  rw [mapHomotopyCategoryδNatTrans_app_app, mapHomotopyCategoryδNatTrans_app_app]
  exact h

open HomotopyCategory in
/-- The comonoidal comparison of `F ⋙ G` in the homotopy category is the comparison of `F`
followed by the comparison of `G`. -/
lemma mapHomotopyCategoryδNatTrans_comp (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [F.IsLeftAdjoint] [G.IsLeftAdjoint] [F.OplaxMonoidal] [G.OplaxMonoidal]
    (X₁ X₂ : HomotopyCategory C (.up ℤ)) :
    ((mapHomotopyCategoryδNatTrans (.up ℤ) (F ⋙ G)).app X₁).app X₂ =
      (G.mapHomotopyCategory _).map (((mapHomotopyCategoryδNatTrans (.up ℤ) F).app X₁).app X₂) ≫
        ((mapHomotopyCategoryδNatTrans (.up ℤ) G).app
          ((F.mapHomotopyCategory _).obj X₁)).app ((F.mapHomotopyCategory _).obj X₂) := by
  obtain ⟨K, rfl⟩ := quotient_obj_surjective X₁
  obtain ⟨L, rfl⟩ := quotient_obj_surjective X₂
  rw [mapHomotopyCategoryδNatTrans_app_app, mapHomotopyCategoryδNatTrans_app_app,
    mapHomotopyCategory_map]
  erw [mapHomotopyCategoryδNatTrans_app_app]
  rw [← Functor.map_comp, mapHomologicalComplexδNatTrans_comp]
  rfl

end Compatibility
section Derived

open OplaxMonoidal LaxMonoidal

variable {E : Type u₃} [Category.{u + 1} E] [Abelian E] [IsGrothendieckAbelian.{u + 1} E]
  [MonoidalCategory E] [MonoidalPreadditive E] [MonoidalClosed E] [SymmetricCategory E]
  [HasFunctorialFlatResolution E]

section

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

lemma derivedTensorLeftDerivedCounit_app_app (X₁ X₂ : HomotopyCategory C (.up ℤ)) :
    ((derivedTensorLeftDerivedCounit F).app X₁).app X₂ =
      (F.leftDerivedFunctorCounit.app X₁ ⊗ₘ F.leftDerivedFunctorCounit.app X₂) ≫
        μ Qh ((F.mapHomotopyCategory _).obj X₁) ((F.mapHomotopyCategory _).obj X₂) := by
  simp [derivedTensorLeftDerivedCounit, tensorHom_def]

lemma leftDerivedDerivedTensorCounit_app_app (X₁ X₂ : HomotopyCategory C (.up ℤ)) :
    ((leftDerivedDerivedTensorCounit F).app X₁).app X₂ =
      F.leftDerivedFunctor.map (μ Qh X₁ X₂) ≫ F.leftDerivedFunctorCounit.app (X₁ ⊗ X₂) := by
  simp [leftDerivedDerivedTensorCounit]

variable [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal]

/-- The characterising property of `leftDerivedTensorComparison`, with tensor products of
morphisms. -/
@[reassoc]
lemma leftDerivedTensorComparison_app_app_comp_tensorHom (X₁ X₂ : HomotopyCategory C (.up ℤ)) :
    ((F.leftDerivedTensorComparison.app (Qh.obj X₁)).app (Qh.obj X₂)) ≫
        (F.leftDerivedFunctorCounit.app X₁ ⊗ₘ F.leftDerivedFunctorCounit.app X₂) ≫
        μ Qh ((F.mapHomotopyCategory _).obj X₁) ((F.mapHomotopyCategory _).obj X₂) =
      F.leftDerivedFunctor.map (μ Qh X₁ X₂) ≫ F.leftDerivedFunctorCounit.app (X₁ ⊗ X₂) ≫
        Qh.map (((mapHomotopyCategoryδNatTrans (.up ℤ) F).app X₁).app X₂) := by
  have := F.leftDerivedTensorComparison_app_app_comp_counit X₁ X₂
  rw [derivedTensorLeftDerivedCounit_app_app, leftDerivedDerivedTensorCounit_app_app] at this
  simpa using this

end

section NatIso

variable {F F' : C ⥤ D} [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal]
  [F'.Additive] [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
  [F'.PreservesFlat] [F'.IsLeftAdjoint] [F'.Monoidal]

/-- A monoidal natural isomorphism `τ : F ≅ F'` carries the tensor comparison of `LF` to the
one of `LF'`, as natural transformations of bifunctors. -/
lemma leftDerivedTensorComparison_naturality (τ : F ≅ F') [NatTrans.IsMonoidal τ.hom] :
    (postcompose₂.map (F.leftDerivedFunctorNatIso τ).hom).app (curriedTensor _) ≫
        F'.leftDerivedTensorComparison =
      F.leftDerivedTensorComparison ≫
        (((whiskeringLeft₂ _).map (F.leftDerivedFunctorNatIso τ).hom).app
          F.leftDerivedFunctor).app (curriedTensor _) ≫
        (((whiskeringLeft₂ _).obj F'.leftDerivedFunctor).map
          (F.leftDerivedFunctorNatIso τ).hom).app (curriedTensor _) := by
  apply leftDerived₂_ext (derivedTensorLeftDerived F') (derivedTensorLeftDerivedCounit F')
    (HomotopyCategory.quasiIso _ _) (HomotopyCategory.quasiIso _ _)
  ext X₁ X₂
  dsimp
  simp only [Category.assoc]
  rw [derivedTensorLeftDerivedCounit_app_app, leftDerivedTensorComparison_app_app_comp_tensorHom,
    ← tensorHom_def_assoc, tensorHom_comp_tensorHom_assoc,
    leftDerivedFunctorNatIso_hom_app_comp_counit, leftDerivedFunctorNatIso_hom_app_comp_counit,
    ← tensorHom_comp_tensorHom_assoc, μ_natural,
    leftDerivedTensorComparison_app_app_comp_tensorHom_assoc,
    ← Qh.map_comp, ← mapHomotopyCategoryδNatTrans_naturality, Qh.map_comp,
    ← leftDerivedFunctorNatIso_hom_app_comp_counit_assoc]
  erw [← NatTrans.naturality_assoc]

end NatIso

section Comp

instance preservesFlat_comp (F : C ⥤ D) (G : D ⥤ E) [F.PreservesFlat] [G.PreservesFlat] :
    (F ⋙ G).PreservesFlat :=
  ⟨fun hX ↦ PreservesFlat.flat_obj (F := G) (PreservesFlat.flat_obj (F := F) hX)⟩

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal]
  (G : D ⥤ E) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [G.PreservesFlat] [G.IsLeftAdjoint] [G.Monoidal]

/-- The naturality of the tensor comparison of `LF`, with tensor products of morphisms. -/
@[reassoc]
lemma leftDerivedTensorComparison_naturality_tensorHom {K₁ K₂ M₁ M₂ : DerivedCategory C}
    (f : K₁ ⟶ K₂) (g : M₁ ⟶ M₂) :
    F.leftDerivedFunctor.map (f ⊗ₘ g) ≫ (F.leftDerivedTensorComparison.app K₂).app M₂ =
      (F.leftDerivedTensorComparison.app K₁).app M₁ ≫
        (F.leftDerivedFunctor.map f ⊗ₘ F.leftDerivedFunctor.map g) := by
  have h₁ := congr_app (F.leftDerivedTensorComparison.naturality f) M₁
  have h₂ := (F.leftDerivedTensorComparison.app K₂).naturality g
  dsimp at h₁ h₂
  rw [tensorHom_def, Functor.map_comp, Category.assoc, h₂, reassoc_of% h₁, tensorHom_def]

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- The tensor comparison of `L(F ⋙ G)` is, through `L(F ⋙ G) ≅ LF ⋙ LG`, the tensor
comparison of `LF` followed by the tensor comparison of `LG`, as natural transformations of
bifunctors. -/
lemma leftDerivedTensorComparison_comp :
    (F ⋙ G).leftDerivedTensorComparison =
      (postcompose₂.map (F.leftDerivedFunctorCompIso G).hom).app (curriedTensor _) ≫
        (postcompose₂.obj G.leftDerivedFunctor).map F.leftDerivedTensorComparison ≫
        (((whiskeringLeft₂ _).obj F.leftDerivedFunctor).obj F.leftDerivedFunctor).map
          G.leftDerivedTensorComparison ≫
        (((whiskeringLeft₂ _).map (F.leftDerivedFunctorCompIso G).inv).app
          (F.leftDerivedFunctor ⋙ G.leftDerivedFunctor)).app (curriedTensor _) ≫
        (((whiskeringLeft₂ _).obj (F ⋙ G).leftDerivedFunctor).map
          (F.leftDerivedFunctorCompIso G).inv).app (curriedTensor _) := by
  apply leftDerived₂_ext (derivedTensorLeftDerived (F ⋙ G))
    (derivedTensorLeftDerivedCounit (F ⋙ G))
    (HomotopyCategory.quasiIso _ _) (HomotopyCategory.quasiIso _ _)
  ext X₁ X₂
  dsimp
  simp only [Category.assoc]
  have k (X : HomotopyCategory C (.up ℤ)) :
      (F.leftDerivedFunctorCompIso G).inv.app (Qh.obj X) ≫
          (F ⋙ G).leftDerivedFunctorCounit.app X =
        G.leftDerivedFunctor.map (F.leftDerivedFunctorCounit.app X) ≫
          G.leftDerivedFunctorCounit.app ((F.mapHomotopyCategory _).obj X) := by
    rw [← leftDerivedFunctorCompIso_hom_app_comp_counit, Iso.inv_hom_id_app_assoc]
  rw [derivedTensorLeftDerivedCounit_app_app, leftDerivedTensorComparison_app_app_comp_tensorHom,
    ← tensorHom_def_assoc, tensorHom_comp_tensorHom_assoc, k, k,
    ← tensorHom_comp_tensorHom_assoc]
  have n := leftDerivedTensorComparison_naturality_tensorHom G
    (F.leftDerivedFunctorCounit.app X₁) (F.leftDerivedFunctorCounit.app X₂)
  have c := leftDerivedTensorComparison_app_app_comp_tensorHom G
    ((F.mapHomotopyCategory _).obj X₁) ((F.mapHomotopyCategory _).obj X₂)
  rw [← reassoc_of% n]
  erw [c]
  have cF := leftDerivedTensorComparison_app_app_comp_tensorHom F X₁ X₂
  have nG := G.leftDerivedFunctorCounit.naturality
    (((mapHomotopyCategoryδNatTrans (.up ℤ) F).app X₁).app X₂)
  have ne := (F.leftDerivedFunctorCompIso G).hom.naturality (μ Qh X₁ X₂)
  dsimp at nG ne
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Category.assoc, cF,
    Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, reassoc_of% nG,
    ← reassoc_of% ne, leftDerivedFunctorCompIso_hom_app_comp_counit_assoc,
    mapHomotopyCategoryδNatTrans_comp, Qh.map_comp]

end Comp

end Derived

end CategoryTheory.Functor
