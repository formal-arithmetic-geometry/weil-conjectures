/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Sheaf.Paper.IntegralResidueDerivedMonoidal
public import WeilConjectures.Algebra.Homology.HomotopyCategory.OplaxMonoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule

import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
import Sheaf.Paper.InverseImageModuleFlat

/-!

# The monoidal structure of the derived pullback on module objects over `Λ`

Let `Λ` be a commutative condensed ring and `f : X ⟶ Y` a morphism of schemes. The derived
pullback `Lf^* = L((f)^*⟦Λ⟧) : D(Mod_{Λ_Y}) ⥤ D(Mod_{Λ_X})` of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar` is strong monoidal for
the derived tensor products `- ⊗ᴸ_{Λ} -` of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor`:
```
m_{K,L} : Lf^* (K ⊗ᴸ_{Λ_Y} L) ≅ Lf^* K ⊗ᴸ_{Λ_X} Lf^* L,    Lf^* Λ_Y ≅ Λ_X.
```
This comparison is the input of the derived projection morphisms, hence of Verdier duality and
Poincaré duality.

The pullback `f^*` of module objects over `Λ` is strong monoidal for the relative tensor products
(`ProEtale.CondensedRing.monoidal_upperStar`), with comparison isomorphisms
`μ : f^* M ⊗_{Λ_X} f^* N ≅ f^* (M ⊗_{Λ_Y} N)`. The comparison `m` is constructed from `μ`
(`ProEtale.CondensedRing.leftDerivedUpperStarTensorIso`) in three steps:

1. **Complexes.** For complexes `A` and `B` of module objects over `Λ_Y`, `μ` applied degreewise
   gives a map of complexes `f^* A ⊗ f^* B ⟶ f^* (A ⊗ B)` for the total tensor product of
   complexes (`ProEtale.CondensedRing.upperStarTensorComplexHom`): on the summand
   `f^* A^p ⊗ f^* B^q` of degree `n = p + q` it is `μ` followed by the inclusion of
   `f^* (A^p ⊗ B^q)` into `f^* ((A ⊗ B)^n)`.
2. **Homotopy category.** Composing with the lax structure `Qh A' ⊗ᴸ Qh B' ⟶ Qh (A' ⊗ B')` of
   the localization `Qh : K(Mod_{Λ_X}) ⥤ D(Mod_{Λ_X})`, this gives a natural transformation of
   bifunctors `Qh (f^* A) ⊗ᴸ Qh (f^* B) ⟶ Qh (f^* (A ⊗ B))` on the homotopy category of
   `Mod_{Λ_Y}` (`ProEtale.CondensedRing.upperStarTensorCounit`).
3. **Derived categories.** The bifunctor `(K, L) ↦ Lf^* K ⊗ᴸ Lf^* L` on `D(Mod_{Λ_Y})`, with the
   transformation of step 2 precomposed with the counits of `Lf^*`, is a left derived bifunctor
   of `(A, B) ↦ Qh (f^* (A ⊗ B))` (`ProEtale.CondensedRing.isLeftDerivedFunctor₂_upperStarTensor`).
   The bifunctor `(K, L) ↦ Lf^* (K ⊗ᴸ L)` receives a canonical transformation to the same
   bifunctor, so the universal property of left derived bifunctors
   (`Functor.leftDerived₂Lift`) gives the comparison
   `m : Lf^* (- ⊗ᴸ -) ⟶ Lf^* - ⊗ᴸ Lf^* -` (`ProEtale.CondensedRing.leftDerivedUpperStarTensor`),
   characterized by its compatibility with the counits.

The unit comparison `ProEtale.CondensedRing.leftDerivedUpperStarUnitIso` is
`Lf^* (Qh 𝟙) ≅ Qh (f^* 𝟙) ≅ Qh 𝟙`: the counit of `Lf^*`, an isomorphism since `f^*` is exact,
followed by the unit comparison of `monoidal_upperStar` in degree `0`. Together with the inverse
of `m` as tensorator, it makes `Lf^*` strong monoidal
(`ProEtale.CondensedRing.monoidal_leftDerivedUpperStar`).

## Sorried input

All the data is constructed; the following properties are `sorry`ed.

- `ProEtale.CondensedRing.upperStarTensorComplexHom_comm`: the degreewise maps of step 1
  commute with the differentials. This is the naturality of `μ` together with the additivity of
  `f^*`.
- the naturality of the transformations `upperStarTensorCounit` and
  `leftDerivedUpperStarTensorLeftCounit` (in both variables): the naturality of `μ`, of the lax
  structure of `Qh` and of the counit of `Lf^*`, checked on representatives in the homotopy
  category.
- `ProEtale.CondensedRing.isLeftDerivedFunctor₂_upperStarTensor`: the bifunctor
  `Lf^* - ⊗ᴸ Lf^* -` is a left derived bifunctor. It is computed on pairs of K-flat complexes,
  `f^*` preserving K-flat complexes; on such a pair both the counits of `Lf^*` and the lax
  structure of `Qh` are isomorphisms.
- `ProEtale.CondensedRing.isIso_leftDerivedUpperStarTensor`: the comparison `m` is an
  isomorphism. On a pair of K-flat complexes both sides are computed by `f^* A ⊗ f^* B` and
  `f^* (A ⊗ B)`, and `m` is induced by `μ`, an isomorphism.
- the associativity and the unitality of `monoidal_leftDerivedUpperStar`. They are checked on
  pairs (resp. triples) of K-flat complexes, where all the comparisons are induced by the
  coherent tensorator `μ`.

## Main definitions

- `ProEtale.CondensedRing.leftDerivedUpperStarTensor`: the comparison
  `Lf^* (K ⊗ᴸ L) ⟶ Lf^* K ⊗ᴸ Lf^* L`, as a natural transformation of bifunctors.
- `ProEtale.CondensedRing.leftDerivedUpperStarTensorIso`: the comparison isomorphism.
- `ProEtale.CondensedRing.leftDerivedUpperStarUnitIso`: the unit comparison `Lf^* 𝟙 ≅ 𝟙`.
- `ProEtale.CondensedRing.monoidal_leftDerivedUpperStar`: the strong monoidal structure on `Lf^*`.

-/

/- The historical sorried-input list above is now discharged by the canonical tensor
transformations and derived monoidal descent constructed below. -/

@[expose] public section

universe u v v₁ v₂

open CategoryTheory Limits MonoidalCategory

private lemma mapCochainComplexμIso_hom_f_eq_desc
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    [MonoidalCategory C] [MonoidalCategory D] [HasZeroObject C] [HasZeroObject D]
    [MonoidalPreadditive C] [MonoidalPreadditive D]
    [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
    [∀ (X₁ X₂ : GradedObject ℤ D), X₁.HasTensor X₂]
    [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
    [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
    [∀ X₁, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).obj X₁)]
    [∀ X₂, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).flip.obj X₂)]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    (G : C ⥤ D) [G.Additive] [G.Monoidal]
    [∀ j, PreservesColimitsOfShape
      (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) G]
    (K L : CochainComplex C ℤ) (n : ℤ) :
    (G.mapCochainComplexμIso K L).hom.f n =
      HomologicalComplex.mapBifunctorDesc (fun p q h ↦
        Functor.LaxMonoidal.μ G (K.X p) (L.X q) ≫
          G.map (HomologicalComplex.ιTensorObj K L p q n h)) := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  rw [HomologicalComplex.ι_mapBifunctorDesc]
  exact Functor.ιTensorObj_mapCochainComplexμIso_hom_f G K L p q n h

private lemma mapCochainComplexDesc_comm
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    [MonoidalCategory C] [MonoidalCategory D] [HasZeroObject C] [HasZeroObject D]
    [MonoidalPreadditive C] [MonoidalPreadditive D]
    [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
    [∀ (X₁ X₂ : GradedObject ℤ D), X₁.HasTensor X₂]
    [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
    [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
    [∀ X₁, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).obj X₁)]
    [∀ X₂, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).flip.obj X₂)]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    (G : C ⥤ D) [G.Additive] [G.Monoidal]
    [∀ j, PreservesColimitsOfShape
      (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) G]
    (K L : CochainComplex C ℤ) (n n' : ℤ)
    (h : (ComplexShape.up ℤ).Rel n n') :
    HomologicalComplex.mapBifunctorDesc (fun p q hpq ↦
        Functor.LaxMonoidal.μ G (K.X p) (L.X q) ≫
          G.map (HomologicalComplex.ιTensorObj K L p q n hpq)) ≫
      ((G.mapHomologicalComplex (.up ℤ)).obj (K ⊗ L)).d n n' =
    ((G.mapHomologicalComplex (.up ℤ)).obj K ⊗
        (G.mapHomologicalComplex (.up ℤ)).obj L).d n n' ≫
      HomologicalComplex.mapBifunctorDesc (fun p q hpq ↦
        Functor.LaxMonoidal.μ G (K.X p) (L.X q) ≫
          G.map (HomologicalComplex.ιTensorObj K L p q n' hpq)) := by
  simpa only [mapCochainComplexμIso_hom_f_eq_desc] using
    (G.mapCochainComplexμIso K L).hom.comm' n n' h

/-- Apply a natural transformation in both tensor factors, then a tensor comparison. -/
noncomputable def CategoryTheory.Functor.tensorCounitOfNatTrans
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [MonoidalCategory E] (L : C ⥤ D) (F : D ⥤ E) (G : C ⥤ E)
    (τ : L ⋙ F ⟶ G) (T : C ⥤ C ⥤ E)
    (α : (((Functor.whiskeringLeft₂ E).obj G).obj G).obj (curriedTensor E) ⟶ T) :
    (((Functor.whiskeringLeft₂ E).obj L).obj L).obj
      ((((Functor.whiskeringLeft₂ E).obj F).obj F).obj (curriedTensor E)) ⟶ T :=
  (((Functor.whiskeringLeft₂ E).map τ).app (L ⋙ F)).app (curriedTensor E) ≫
    (((Functor.whiskeringLeft₂ E).obj G).map τ).app (curriedTensor E) ≫ α

private lemma isIso_tensorCounit_app_app
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [MonoidalCategory E] (L : C ⥤ D) (F : D ⥤ E) (G : C ⥤ E)
    (T : C ⥤ C ⥤ E) (τ : L ⋙ F ⟶ G) [IsIso τ]
    (α : (((Functor.whiskeringLeft₂ _).obj G).obj G).obj (curriedTensor _) ⟶ T)
    (A B : C) [IsIso ((α.app A).app B)] :
    IsIso (((Functor.tensorCounitOfNatTrans L F G τ T α).app A).app B) := by
  change IsIso ((τ.app A ▷ F.obj (L.obj B)) ≫
    (G.obj A ◁ τ.app B) ≫ (α.app A).app B)
  infer_instance

private lemma isLeftDerivedFunctor₂_tensorCounit
    {C : Type v₁} [Category.{v + 1} C] [Abelian C] [IsGrothendieckAbelian.{v + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    {D : Type v₂} [Category.{v + 1} D] [Abelian D] [IsGrothendieckAbelian.{v + 1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    [Abelian.HasFunctorialFlatResolution D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.PreservesFlat] [F.IsLeftAdjoint]
    (T : HomotopyCategory C (.up ℤ) ⥤ HomotopyCategory C (.up ℤ) ⥤ DerivedCategory D)
    (α : (((Functor.whiskeringLeft₂ _).obj
      (F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)).obj
        (F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)).obj (curriedTensor _) ⟶ T)
    (hα : ∀ A B, F.kFlatMap B → IsIso ((α.app A).app B)) :
    (Functor.derivedTensorLeftDerived F).IsLeftDerivedFunctor₂
      (Functor.tensorCounitOfNatTrans DerivedCategory.Qh F.leftDerivedFunctor
        (F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) F.leftDerivedFunctorCounit T α)
      (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) := by
  refine LocalizerMorphism.isLeftDerivedFunctor₂_of_isLeftDerivabilityStructure
    (HomotopyCategory.quasiIsoLocalizerMorphism F.kFlatMap)
    (HomotopyCategory.quasiIsoLocalizerMorphism F.kFlatMap) _ ?_
  intro A B
  have : IsIso ((α.app A.obj).app B.obj) := hα A.obj B.obj B.property
  exact isIso_tensorCounit_app_app DerivedCategory.Qh F.leftDerivedFunctor
    (F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) T F.leftDerivedFunctorCounit α
    A.obj B.obj

/-- The tensorator of an additive monoidal functor, passed to the homotopy category
and followed by the lax tensorator of the derived localization. -/
noncomputable def CategoryTheory.Functor.homotopyTensorCounit
    {C : Type v₁} [Category.{v + 1} C] [Abelian C] [IsGrothendieckAbelian.{v + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    {D : Type v₂} [Category.{v + 1} D] [Abelian D] [IsGrothendieckAbelian.{v + 1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    [Abelian.HasFunctorialFlatResolution D]
    (F : C ⥤ D) [F.Additive]
    [F.IsLeftAdjoint] [F.Monoidal]
    : (((Functor.whiskeringLeft₂ _).obj
        (F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)).obj
          (F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)).obj (curriedTensor _) ⟶
      (Functor.postcompose₂.obj
        (F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)).obj (curriedTensor _) :=
  (((Functor.whiskeringLeft₂ _).obj (F.mapHomotopyCategory (.up ℤ))).obj
      (F.mapHomotopyCategory (.up ℤ))).map
        (Functor.LaxMonoidal.μNatTrans DerivedCategory.Qh) ≫
    (Functor.postcompose₂.obj DerivedCategory.Qh).map
      (asIso (Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) F)).inv

private lemma isIso_homotopyTensorCounit
    {C : Type v₁} [Category.{v + 1} C] [Abelian C] [IsGrothendieckAbelian.{v + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    {D : Type v₂} [Category.{v + 1} D] [Abelian D] [IsGrothendieckAbelian.{v + 1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    [Abelian.HasFunctorialFlatResolution D]
    (F : C ⥤ D) [F.Additive]
    [F.IsLeftAdjoint] [F.Monoidal]
    (A B : HomotopyCategory C (.up ℤ)) (hB : F.kFlatMap B) :
    IsIso (((F.homotopyTensorCounit).app A).app B) := by
  have hμ := Functor.isIso_μNatTrans_Qh_app_app_of_kFlat
    ((F.mapHomotopyCategory (.up ℤ)).obj A) _ hB
  exact IsIso.comp_isIso' hμ (Functor.map_isIso DerivedCategory.Qh
    (((asIso (Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) F)).inv.app A).app B))

/-- The counit of the derived tensor of two left derived functors, followed by the
homotopy-category tensor comparison. -/
noncomputable def CategoryTheory.Functor.homotopyTensorLeftDerivedCounit
    {C : Type v₁} [Category.{v + 1} C] [Abelian C] [IsGrothendieckAbelian.{v + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    {D : Type v₂} [Category.{v + 1} D] [Abelian D] [IsGrothendieckAbelian.{v + 1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    [Abelian.HasFunctorialFlatResolution D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.IsLeftAdjoint] [F.Monoidal]
    : (((Functor.whiskeringLeft₂ _).obj DerivedCategory.Qh).obj DerivedCategory.Qh).obj
        (Functor.derivedTensorLeftDerived F) ⟶
      (Functor.postcompose₂.obj
        (F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)).obj (curriedTensor _) :=
  Functor.tensorCounitOfNatTrans DerivedCategory.Qh F.leftDerivedFunctor
    (F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) F.leftDerivedFunctorCounit _
    F.homotopyTensorCounit

private lemma isLeftDerivedFunctor₂_homotopyTensorLeftDerivedCounit
    {C : Type v₁} [Category.{v + 1} C] [Abelian C] [IsGrothendieckAbelian.{v + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    {D : Type v₂} [Category.{v + 1} D] [Abelian D] [IsGrothendieckAbelian.{v + 1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    [Abelian.HasFunctorialFlatResolution D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.IsLeftAdjoint] [F.Monoidal]
    [F.PreservesFlat] :
    (Functor.derivedTensorLeftDerived F).IsLeftDerivedFunctor₂
      F.homotopyTensorLeftDerivedCounit
      (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) :=
  isLeftDerivedFunctor₂_tensorCounit F _ F.homotopyTensorCounit
    (fun A B hB ↦ isIso_homotopyTensorCounit F A B hB)

private lemma isIso_leftDerivedBifunctorLift
    {C₁ C₂ D₁ D₂ E : Type*} [Category* C₁] [Category* C₂]
    [Category* D₁] [Category* D₂] [Category* E]
    {L₁ : C₁ ⥤ D₁} {L₂ : C₂ ⥤ D₂}
    (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
    [L₁.IsLocalization W₁] [L₂.IsLocalization W₂]
    [W₁.ContainsIdentities] [W₂.ContainsIdentities]
    (T : C₁ ⥤ C₂ ⥤ E) (F G : D₁ ⥤ D₂ ⥤ E)
    (α : (((Functor.whiskeringLeft₂ E).obj L₁).obj L₂).obj F ⟶ T)
    (β : (((Functor.whiskeringLeft₂ E).obj L₁).obj L₂).obj G ⟶ T)
    [hF : F.IsLeftDerivedFunctor₂ α W₁ W₂] [hG : G.IsLeftDerivedFunctor₂ β W₁ W₂] :
    IsIso (F.leftDerived₂Lift α W₁ W₂ G β) := by
  have h : F.leftDerived₂Lift α W₁ W₂ G β =
      Functor.leftDerived₂NatTrans F α W₁ W₂ G β (𝟙 T) := by
    simp only [Functor.leftDerived₂NatTrans, Category.comp_id]
  rw [h]
  infer_instance

/-- The tensor-unit comparison for the left derived functor of an exact monoidal functor. -/
noncomputable def CategoryTheory.Functor.leftDerivedTensorUnitIso
    {C : Type v₁} [Category.{v + 1} C] [Abelian C] [IsGrothendieckAbelian.{v + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    {D : Type v₂} [Category.{v + 1} D] [Abelian D] [IsGrothendieckAbelian.{v + 1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    [Abelian.HasFunctorialFlatResolution D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.IsLeftAdjoint] [F.Monoidal]
    : F.leftDerivedFunctor.obj (𝟙_ _) ≅ 𝟙_ _ :=
  asIso (F.leftDerivedFunctorCounit.app (𝟙_ _)) ≪≫
    DerivedCategory.Qh.mapIso
      ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app (𝟙_ _) ≪≫
        (HomotopyCategory.quotient _ _).mapIso
          ((HomologicalComplex.singleMapHomologicalComplex F
              (ComplexShape.up ℤ) 0).app (𝟙_ _) ≪≫
            (HomologicalComplex.single _ _ 0).mapIso (Functor.Monoidal.εIso F).symm))

private lemma leftDerivedLift_eq_of_inverse
    {C₁ C₂ D₁ D₂ E : Type*} [Category* C₁] [Category* C₂]
    [Category* D₁] [Category* D₂] [Category* E]
    {L₁ : C₁ ⥤ D₁} {L₂ : C₂ ⥤ D₂}
    (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
    [L₁.IsLocalization W₁] [L₂.IsLocalization W₂]
    [W₁.ContainsIdentities] [W₂.ContainsIdentities]
    {S T : C₁ ⥤ C₂ ⥤ E} (F G : D₁ ⥤ D₂ ⥤ E)
    (α : (((Functor.whiskeringLeft₂ E).obj L₁).obj L₂).obj F ⟶ S)
    (α' : (((Functor.whiskeringLeft₂ E).obj L₁).obj L₂).obj F ⟶ T)
    (β : (((Functor.whiskeringLeft₂ E).obj L₁).obj L₂).obj G ⟶ T)
    [F.IsLeftDerivedFunctor₂ α W₁ W₂] [F.IsLeftDerivedFunctor₂ α' W₁ W₂]
    (δ : T ⟶ S) (ε : S ⟶ T) (h : α' = α ≫ ε) (hδε : δ ≫ ε = 𝟙 T) :
    F.leftDerived₂Lift α' W₁ W₂ G β = F.leftDerived₂NatTrans α W₁ W₂ G β δ := by
  apply Functor.leftDerived₂_ext F α' W₁ W₂
  rw [Functor.leftDerived₂_fac, h, ← Category.assoc, Functor.leftDerived₂NatTrans_fac,
    Category.assoc, hδε, Category.comp_id]

namespace CategoryTheory.Functor
open DerivedCategory LaxMonoidal OplaxMonoidal
variable {C : Type v₁} [Category.{v + 1} C] [Abelian C] [IsGrothendieckAbelian.{v + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]
  {D : Type v₂} [Category.{v + 1} D] [Abelian D] [IsGrothendieckAbelian.{v + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [Abelian.HasFunctorialFlatResolution D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.IsLeftAdjoint] [F.Monoidal] [F.PreservesFlat]

/-- The descended unit map is the counit followed by the ordinary unit comparison in degree zero. -/
lemma residueDerivedOplax_η_eq_tensorUnitIso :
    letI := residueDerivedOplax F
    η F.leftDerivedFunctor = (leftDerivedTensorUnitIso F).hom := by
  have := DerivedCategory.isIso_ε_Qh C
  have := DerivedCategory.isIso_ε_Qh D
  have hεC : ε (Qh (C := C)) = 𝟙 _ := rfl
  have hεD : ε (Qh (C := D)) = 𝟙 _ := rfl
  change F.leftDerivedFunctor.map (ε Qh) ≫ F.leftDerivedFunctorCounit.app (𝟙_ _) ≫
    Qh.map (η (F.mapHomotopyCategory (.up ℤ))) ≫ CategoryTheory.inv (ε Qh) = _
  have hmapC : F.leftDerivedFunctor.map (ε (Qh (C := C))) = 𝟙 _ := by
    change F.leftDerivedFunctor.map (𝟙 _) = 𝟙 _
    exact F.leftDerivedFunctor.map_id _
  have hinvD : CategoryTheory.inv (ε (Qh (C := D))) = 𝟙 _ :=
    IsIso.inv_eq_of_hom_inv_id (by simpa only [Category.comp_id] using hεD)
  erw [hmapC, hinvD, Category.id_comp, Category.comp_id]
  simp only [leftDerivedTensorUnitIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, asIso_hom,
    mapHomotopyCategory_η, mapCochainComplex_η, mapCochainComplexεIso,
    Iso.trans_inv, Functor.mapIso_inv]
  congr 1
  apply Qh.congr_map
  change (HomotopyCategory.quotient D (.up ℤ)).map _ = _
  have hh : ((F.mapHomotopyCategoryFactors (.up ℤ)).app (𝟙_ _)).hom = 𝟙 _ := by
    simp [Functor.mapHomotopyCategoryFactors]
    rfl
  erw [hh, Category.id_comp]
  rfl

/-- The canonical derived monoidal structure with its unit maps written using the explicit
comparison `leftDerivedTensorUnitIso`. This preserves the definitional unit API. -/
@[instance_reducible]
noncomputable def leftDerivedMonoidalWithUnit : F.leftDerivedFunctor.Monoidal :=
  letI := residueDerivedMonoidal F
  have hη : η F.leftDerivedFunctor = (leftDerivedTensorUnitIso F).hom :=
    residueDerivedOplax_η_eq_tensorUnitIso F
  have hε : (leftDerivedTensorUnitIso F).inv = ε F.leftDerivedFunctor := by
    apply (cancel_mono (leftDerivedTensorUnitIso F).hom).1
    rw [Iso.inv_hom_id, ← hη, Monoidal.ε_η]
  Monoidal.copy (residueDerivedMonoidal F) (leftDerivedTensorUnitIso F).inv
    (μ F.leftDerivedFunctor) (leftDerivedTensorUnitIso F).hom (δ F.leftDerivedFunctor)
    hε rfl hη.symm rfl


variable [hR : (derivedTensorLeftDerived F).IsLeftDerivedFunctor₂
  F.homotopyTensorLeftDerivedCounit
  (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ))]

omit [F.PreservesFlat] hR in
private lemma homotopyTensorLeftDerivedCounit_eq :
    F.homotopyTensorLeftDerivedCounit = F.derivedTensorLeftDerivedCounit ≫
    (postcompose₂.obj Qh).map
      (asIso (mapHomotopyCategoryδNatTrans (.up ℤ) F)).inv := by
  ext A B
  change (F.leftDerivedFunctorCounit.app A ▷ F.leftDerivedFunctor.obj (Qh.obj B)) ≫
      (Qh.obj ((F.mapHomotopyCategory (.up ℤ)).obj A) ◁ F.leftDerivedFunctorCounit.app B) ≫
      (μ Qh ((F.mapHomotopyCategory (.up ℤ)).obj A)
        ((F.mapHomotopyCategory (.up ℤ)).obj B) ≫
          Qh.map (((asIso (mapHomotopyCategoryδNatTrans (.up ℤ) F)).inv.app A).app B)) =
    ((F.leftDerivedFunctorCounit.app A ▷ F.leftDerivedFunctor.obj (Qh.obj B)) ≫
      (Qh.obj ((F.mapHomotopyCategory (.up ℤ)).obj A) ◁ F.leftDerivedFunctorCounit.app B) ≫
      μ Qh ((F.mapHomotopyCategory (.up ℤ)).obj A)
        ((F.mapHomotopyCategory (.up ℤ)).obj B)) ≫
      Qh.map (((asIso (mapHomotopyCategoryδNatTrans (.up ℤ) F)).inv.app A).app B)
  simp only [Category.assoc]

omit [F.PreservesFlat] hR [Abelian.HasFunctorialFlatResolution C]
  [Abelian.HasFunctorialFlatResolution D] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F] in
private lemma homotopyTensorComparison_hom_inv : (postcompose₂MapWhiskeringLeft₂
    (mapHomotopyCategoryδNatTrans (.up ℤ) F) Qh) ≫
    ((postcompose₂.obj Qh).map (asIso (mapHomotopyCategoryδNatTrans (.up ℤ) F)).inv) =
    𝟙 ((postcompose₂.obj (F.mapHomotopyCategory (.up ℤ) ⋙ Qh)).obj (curriedTensor _)) := by
  ext A B
  change Qh.map (((mapHomotopyCategoryδNatTrans (.up ℤ) F).app A).app B) ≫
    Qh.map (((asIso (mapHomotopyCategoryδNatTrans (.up ℤ) F)).inv.app A).app B) = 𝟙 _
  rw [← Qh.map_comp]
  have h := (asIso (mapHomotopyCategoryδNatTrans (.up ℤ) F)).hom_inv_id_app_app A B
  simp only [asIso_hom] at h
  rw [h, Qh.map_id]

/-- Changing the target tensor counit by the inverse comonoidal comparison leaves the
canonical derived tensor comparison unchanged, by the derived universal property. -/
lemma homotopyTensorLeftDerivedLift_eq :
    (derivedTensorLeftDerived F).leftDerived₂Lift F.homotopyTensorLeftDerivedCounit
      (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ))
      (leftDerivedDerivedTensor F) F.leftDerivedDerivedTensorCounit =
        F.leftDerivedTensorComparison := by
  exact leftDerivedLift_eq_of_inverse
    (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ))
    (derivedTensorLeftDerived F) (leftDerivedDerivedTensor F)
    F.derivedTensorLeftDerivedCounit F.homotopyTensorLeftDerivedCounit
    F.leftDerivedDerivedTensorCounit
    (postcompose₂MapWhiskeringLeft₂ (mapHomotopyCategoryδNatTrans (.up ℤ) F) Qh)
    ((postcompose₂.obj Qh).map (asIso (mapHomotopyCategoryδNatTrans (.up ℤ) F)).inv)
    (homotopyTensorLeftDerivedCounit_eq F) (homotopyTensorComparison_hom_inv F)

end CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open scoped CategoryTheory.Obj

open Scheme Functor

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

/-! ### Instances

Direct instances for complexes of module objects over `Λ_Z`. Finding them from the generic
instances on `Mod` exceeds the default heartbeat limit, so they are recorded once here. -/

-- Cache the ambient existence properties used by every derived functor in the file.
local instance grothendieckModulesShortcut (Z : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1}
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :=
  inferInstance

local instance flatResolutionModulesShortcut (Z : Scheme.{u}) :
    Abelian.HasFunctorialFlatResolution
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :=
  inferInstance

-- Reuse the already available pullback properties throughout these concrete constructions.
local instance upperStarAdditiveShortcut : (f)^*⟦Λ⟧.Additive := inferInstance

local instance upperStarFiniteLimitsShortcut : PreservesFiniteLimits (f)^*⟦Λ⟧ :=
  inferInstance

local instance upperStarFiniteColimitsShortcut : PreservesFiniteColimits (f)^*⟦Λ⟧ :=
  inferInstance

local instance upperStarLeftAdjointShortcut : (f)^*⟦Λ⟧.IsLeftAdjoint := inferInstance

-- Give tensor-colimit inference a direct path in the internal module category.
local instance preservesColimitsTensorLeftShortcut (Z : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :
    PreservesColimitsOfSize.{0, 0} ((curriedTensor _).obj M) :=
  inferInstance

local instance preservesColimitsTensorRightShortcut (Z : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :
    PreservesColimitsOfSize.{0, 0} ((curriedTensor _).flip.obj M) :=
  inferInstance

-- Cache the colimit compatibility proofs used repeatedly by total tensor products.
local instance hasTensorGradedShortcut (Z : Scheme.{u})
    (A B : GradedObject ℤ (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))) : A.HasTensor B :=
  inferInstance

local instance hasGoodTensorLeftShortcut (Z : Scheme.{u})
    (A B C : GradedObject ℤ (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))) : GradedObject.HasGoodTensor₁₂Tensor A B C :=
  inferInstance

local instance hasGoodTensorRightShortcut (Z : Scheme.{u})
    (A B C : GradedObject ℤ (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))) : GradedObject.HasGoodTensorTensor₂₃ A B C :=
  inferInstance

local instance hasTensorFourShortcut (Z : Scheme.{u})
    (A B C D : GradedObject ℤ (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))) : GradedObject.HasTensor₄ObjExt A B C D :=
  inferInstance

set_option synthInstance.maxHeartbeats 200000 in
-- the generic search goes through the colimits of `Mod (Sheaf (ProEt.topology Z) Ab) _`
instance hasTensor_cochainComplex (Z : Scheme.{u})
    (A B : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) ℤ) :
    HomologicalComplex.HasTensor A B :=
  hasTensorGradedShortcut Λ Z A.X B.X

set_option synthInstance.maxHeartbeats 200000 in
-- the generic search goes through the colimits of `Mod (Sheaf (ProEt.topology Z) Ab) _`
noncomputable instance monoidalCategoryStruct_cochainComplex (Z : Scheme.{u}) :
    MonoidalCategoryStruct
      (CochainComplex (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))
        ℤ) :=
  inferInstance

set_option synthInstance.maxHeartbeats 200000 in
-- the generic search goes through the colimits of `Mod (Sheaf (ProEt.topology Z) Ab) _`
noncomputable instance monoidalCategory_cochainComplex (Z : Scheme.{u}) :
    MonoidalCategory
      (CochainComplex (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))
        ℤ) :=
  inferInstance

/-! ### Complexes -/

/-- The degreewise comparison `(f^* A ⊗ f^* B)^n ⟶ f^* ((A ⊗ B)^n)` for complexes `A` and `B`
of module objects over `Λ_Y`: on the summand `f^* A^p ⊗ f^* B^q` with `p + q = n`, the tensorator
`μ : f^* A^p ⊗ f^* B^q ⟶ f^* (A^p ⊗ B^q)` followed by `f^*` of the inclusion of the summand. -/
noncomputable def upperStarTensorComplexHomX
    (A B : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ) (n : ℤ) :
    (((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).obj A ⊗
      ((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).obj B).X n ⟶
      (((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).obj (A ⊗ B)).X n :=
  HomologicalComplex.mapBifunctorDesc fun p q h ↦
    Functor.LaxMonoidal.μ (f)^*⟦Λ⟧ (A.X p) (B.X q) ≫
      (f)^*⟦Λ⟧.map (HomologicalComplex.ιTensorObj A B p q n h)

/-- The degreewise comparisons `upperStarTensorComplexHomX` commute with the differentials. -/
lemma upperStarTensorComplexHom_comm
    (A B : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ) (n n' : ℤ)
    (_ : (ComplexShape.up ℤ).Rel n n') :
    upperStarTensorComplexHomX Λ f A B n ≫
        (((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).obj (A ⊗ B)).d n n' =
      (((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).obj A ⊗
        ((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).obj B).d n n' ≫
        upperStarTensorComplexHomX Λ f A B n' := by
  simpa only [upperStarTensorComplexHomX] using
    mapCochainComplexDesc_comm ((f)^*⟦Λ⟧) A B n n' (by assumption)

/-- The comparison `f^* A ⊗ f^* B ⟶ f^* (A ⊗ B)` of complexes of module objects, induced
degreewise by the tensorator of the strong monoidal pullback `f^*`. -/
noncomputable def upperStarTensorComplexHom
    (A B : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ) :
    ((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).obj A ⊗
        ((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).obj B ⟶
      ((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).obj (A ⊗ B) where
  f n := upperStarTensorComplexHomX Λ f A B n
  comm' n n' h := upperStarTensorComplexHom_comm Λ f A B n n' h

/-! ### The homotopy category -/

/-- The bifunctor `(A, B) ↦ Qh (f^* (A ⊗ B))` on the homotopy category of complexes of module
objects over `Λ_Y`, of which both sides of the comparison are left derived bifunctors. -/
noncomputable def upperStarTensorTarget :
    HomotopyCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
        (ComplexShape.up ℤ) ⥤
      HomotopyCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj Λ Y)) (ComplexShape.up ℤ) ⥤
        DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj Λ X)) :=
  (postcompose₂.obj
    ((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)).obj (curriedTensor _)

/-- The transformation `Qh (f^* A) ⊗ᴸ Qh (f^* B) ⟶ Qh (f^* (A ⊗ B))` of bifunctors on the
homotopy category of `Mod_{Λ_Y}`: the lax structure of `Qh` followed by `Qh` of the comparison
`upperStarTensorComplexHom`. -/
noncomputable def upperStarTensorCounit :
    (((whiskeringLeft₂ _).obj
        ((f)^*⟦Λ⟧.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)).obj
        ((f)^*⟦Λ⟧.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)).obj
        (curriedTensor _) ⟶
      upperStarTensorTarget Λ f :=
  (f)^*⟦Λ⟧.homotopyTensorCounit

/-! ### Derived categories -/

/-- The bifunctor `(K, L) ↦ Lf^* K ⊗ᴸ Lf^* L` on `D(Mod_{Λ_Y})`. -/
noncomputable def leftDerivedUpperStarTensorRight :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ⥤
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj Λ Y)) ⥤
        DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj Λ X)) :=
  Functor.derivedTensorLeftDerived (f)^*⟦Λ⟧

/-- The bifunctor `(K, L) ↦ Lf^* (K ⊗ᴸ L)` on `D(Mod_{Λ_Y})`. -/
noncomputable def leftDerivedUpperStarTensorLeft :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ⥤
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj Λ Y)) ⥤
        DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj Λ X)) :=
  Functor.leftDerivedDerivedTensor (f)^*⟦Λ⟧

/-- The counit of the bifunctor `Lf^* - ⊗ᴸ Lf^* -`: the counits
`Qh ⋙ Lf^* ⟶ f^* ⋙ Qh` of the derived pullback in both variables, followed by
`upperStarTensorCounit`. -/
noncomputable def leftDerivedUpperStarTensorRightCounit :
    (((whiskeringLeft₂ _).obj DerivedCategory.Qh).obj DerivedCategory.Qh).obj
        (leftDerivedUpperStarTensorRight Λ f) ⟶
      upperStarTensorTarget Λ f :=
  (f)^*⟦Λ⟧.homotopyTensorLeftDerivedCounit

/-- Pullback of module objects preserves flat objects. The coefficient ring comparison is an
isomorphism, so extension of scalars identifies with restriction along its inverse. Transport
flatness along this identification and apply `ProEtale.inverseImageModule_preservesFlat`. -/
lemma upperStar_preservesFlat : (f)^*⟦Λ⟧.PreservesFlat := by
  let G := (f)^*[Ab.{u + 1}]
  let R := condensedRingObj Λ Y
  let ρ := (asIso (condensedPullbackHom Λ f)).inv
  have h := ProEtale.inverseImageModule_preservesFlat f R (condensedRingObj Λ X) ρ
  let e : (f)^*⟦Λ⟧ ≅ Mod.mapModComap ρ :=
    Functor.isoWhiskerLeft (G.mapMod R)
      (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f))
  exact ⟨fun hM ↦ (ObjectProperty.flat).prop_of_iso (e.symm.app _) (h.flat_obj hM)⟩

/-- The bifunctor `Lf^* - ⊗ᴸ Lf^* -` is a left derived bifunctor of `(A, B) ↦ Qh (f^* (A ⊗ B))`,
for the counit `leftDerivedUpperStarTensorRightCounit`. See the module docstring. -/
instance isLeftDerivedFunctor₂_upperStarTensor :
    (leftDerivedUpperStarTensorRight Λ f).IsLeftDerivedFunctor₂
      (leftDerivedUpperStarTensorRightCounit Λ f)
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) := by
  have hflat := upperStar_preservesFlat Λ f
  exact isLeftDerivedFunctor₂_homotopyTensorLeftDerivedCounit (f)^*⟦Λ⟧

/-- The counit of the bifunctor `Lf^* (- ⊗ᴸ -)`: `Lf^*` of the lax structure
`Qh A ⊗ᴸ Qh B ⟶ Qh (A ⊗ B)` of the localization, followed by the counit
`Lf^* (Qh (A ⊗ B)) ⟶ Qh (f^* (A ⊗ B))` of the derived pullback. -/
noncomputable def leftDerivedUpperStarTensorLeftCounit :
    (((whiskeringLeft₂ _).obj DerivedCategory.Qh).obj DerivedCategory.Qh).obj
        (leftDerivedUpperStarTensorLeft Λ f) ⟶
      upperStarTensorTarget Λ f :=
  Functor.leftDerivedDerivedTensorCounit (f)^*⟦Λ⟧

/-- The comparison `m_{K,L} : Lf^* (K ⊗ᴸ L) ⟶ Lf^* K ⊗ᴸ Lf^* L` of the derived pullback with the
derived tensor product, as a natural transformation of bifunctors on `D(Mod_{Λ_Y})`: the
morphism to the left derived bifunctor `Lf^* - ⊗ᴸ Lf^* -` induced by the counit
`leftDerivedUpperStarTensorLeftCounit` (`Functor.leftDerived₂Lift`). -/
noncomputable def leftDerivedUpperStarTensor :
    leftDerivedUpperStarTensorLeft Λ f ⟶ leftDerivedUpperStarTensorRight Λ f :=
  @Functor.leftDerived₂Lift _ _ _ _ _ _ _ _ _ _
    (leftDerivedUpperStarTensorRight Λ f) _ DerivedCategory.Qh DerivedCategory.Qh
    (leftDerivedUpperStarTensorRightCounit Λ f)
    (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ))
    inferInstance inferInstance inferInstance inferInstance
    (isLeftDerivedFunctor₂_upperStarTensor Λ f)
    (leftDerivedUpperStarTensorLeft Λ f) (leftDerivedUpperStarTensorLeftCounit Λ f)

/-- The comparison `m` is compatible with the counits. -/
lemma leftDerivedUpperStarTensor_fac :
    (((whiskeringLeft₂ _).obj DerivedCategory.Qh).obj DerivedCategory.Qh).map
        (leftDerivedUpperStarTensor Λ f) ≫ leftDerivedUpperStarTensorRightCounit Λ f =
      leftDerivedUpperStarTensorLeftCounit Λ f :=
  @Functor.leftDerived₂_fac _ _ _ _ _ _ _ _ _ _
    (leftDerivedUpperStarTensorRight Λ f) _ DerivedCategory.Qh DerivedCategory.Qh
    (leftDerivedUpperStarTensorRightCounit Λ f)
    (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ))
    inferInstance inferInstance inferInstance inferInstance
    (isLeftDerivedFunctor₂_upperStarTensor Λ f)
    (leftDerivedUpperStarTensorLeft Λ f) (leftDerivedUpperStarTensorLeftCounit Λ f)

/-- The comparison `m : Lf^* (- ⊗ᴸ -) ⟶ Lf^* - ⊗ᴸ Lf^* -` is an isomorphism. See the module
docstring. -/
instance isIso_leftDerivedUpperStarTensor : IsIso (leftDerivedUpperStarTensor Λ f) := by
  have hright : (Functor.derivedTensorLeftDerived (f)^*⟦Λ⟧).IsLeftDerivedFunctor₂
      (f)^*⟦Λ⟧.homotopyTensorLeftDerivedCounit
      (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) :=
    isLeftDerivedFunctor₂_upperStarTensor Λ f
  have hleft : (Functor.leftDerivedDerivedTensor (f)^*⟦Λ⟧).IsLeftDerivedFunctor₂
      (Functor.leftDerivedDerivedTensorCounit (f)^*⟦Λ⟧)
      (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) :=
    Functor.isLeftDerivedFunctor₂_leftDerivedDerivedTensor (f)^*⟦Λ⟧
  exact isIso_leftDerivedBifunctorLift (hF := hright) (hG := hleft)
    (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ))
    ((Functor.postcompose₂.obj
      ((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)).obj (curriedTensor _))
    (Functor.derivedTensorLeftDerived (f)^*⟦Λ⟧)
    (Functor.leftDerivedDerivedTensor (f)^*⟦Λ⟧)
    (f)^*⟦Λ⟧.homotopyTensorLeftDerivedCounit
    (Functor.leftDerivedDerivedTensorCounit (f)^*⟦Λ⟧)

/-- The tensor comparison defined by the two derived counits is the canonical comonoidal
comparison used by the descended monoidal structure. -/
lemma leftDerivedUpperStarTensor_eq_leftDerivedTensorComparison :
    letI := upperStar_preservesFlat Λ f
    leftDerivedUpperStarTensor Λ f = (f)^*⟦Λ⟧.leftDerivedTensorComparison := by
  have hflat := upperStar_preservesFlat Λ f
  have hright : (Functor.derivedTensorLeftDerived (f)^*⟦Λ⟧).IsLeftDerivedFunctor₂
      (f)^*⟦Λ⟧.homotopyTensorLeftDerivedCounit
      (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) :=
    isLeftDerivedFunctor₂_upperStarTensor Λ f
  exact Functor.homotopyTensorLeftDerivedLift_eq (f)^*⟦Λ⟧

/-- The comparison isomorphism `m_{K,L} : Lf^* (K ⊗ᴸ L) ≅ Lf^* K ⊗ᴸ Lf^* L` of the derived
pullback with the derived tensor product. -/
noncomputable def leftDerivedUpperStarTensorIso :
    leftDerivedUpperStarTensorLeft Λ f ≅ leftDerivedUpperStarTensorRight Λ f :=
  asIso (leftDerivedUpperStarTensor Λ f)

/-! ### The monoidal structure -/

/-- The derived pullback of the tensor unit `Λ_Y` is the tensor unit `Λ_X`: the counit
`Lf^* (Qh 𝟙) ≅ Qh (f^* 𝟙)` of the derived pullback of the exact functor `f^*`, followed by the
unit comparison `f^* 𝟙 ≅ 𝟙` of the strong monoidal pullback of module objects, in degree `0`. -/
noncomputable def leftDerivedUpperStarUnitIso :
    L((f)^*⟦Λ⟧).obj (𝟙_ _) ≅ 𝟙_ _ :=
  (f)^*⟦Λ⟧.leftDerivedTensorUnitIso

/-- The derived pullback `Lf^* : D(Mod_{Λ_Y}) ⥤ D(Mod_{Λ_X})` on module objects over `Λ` is
strong monoidal for the derived tensor products, with tensorator the inverse of
`leftDerivedUpperStarTensorIso` and unit comparison `leftDerivedUpperStarUnitIso`. -/
noncomputable instance monoidal_leftDerivedUpperStar : L((f)^*⟦Λ⟧).Monoidal := by
  have hflat := upperStar_preservesFlat Λ f
  exact Functor.leftDerivedMonoidalWithUnit (f)^*⟦Λ⟧

end AlgebraicGeometry.ProEtale.CondensedRing
