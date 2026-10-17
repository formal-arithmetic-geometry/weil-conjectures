/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat

/-!
# The tensor comparison of the left derived functor of a right exact monoidal functor

Let `F : C ⥤ D` be a strong monoidal functor between monoidal Grothendieck abelian categories
with functorial flat resolutions, which is a left adjoint, preserves flat objects and sends
quasi-isomorphisms between K-flat complexes to quasi-isomorphisms, but need not be exact (for
instance, extension of scalars along a quotient map of rings). Its total left derived functor
`LF` is then still monoidal: the comonoidal structure `δ` of `F` derives to a natural
isomorphism `LF(K ⊗ᴸ M) ≅ LF K ⊗ᴸ LF M`.

This generalises `CategoryTheory.Functor.leftDerivedTensorComparison`, which is the case of an
exact `F`. Both bifunctors are computed on pairs of complexes which are K-flat and whose image
under `F` is K-flat; these form a left derivability structure, the functorial flat resolutions
being such complexes.

## Main definitions and results

- `CategoryTheory.Functor.kFlatInterKFlatMap F`: the K-flat complexes whose image under `F` is
  K-flat; they form a left derivability structure.
- `CategoryTheory.Functor.leftDerivedTensorComparisonOfKFlat F`: the comparison
  `LF(K ⊗ᴸ M) ⟶ LF K ⊗ᴸ LF M`, an isomorphism.
-/

@[expose] public section

universe u u₁ u₂

open CategoryTheory Abelian Limits MonoidalCategory DerivedCategory

open scoped CategoryTheory.Functor

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasFunctorialFlatResolution C]
  {D : Type u₂} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [HasFunctorialFlatResolution D]

section

variable (F : C ⥤ D) [F.Additive]

/-- The K-flat complexes in `K(C)` whose image under `F : C ⥤ D` is K-flat. -/
abbrev kFlatInterKFlatMap : ObjectProperty (HomotopyCategory C (.up ℤ)) :=
  (HomotopyCategory.quasiIso C (.up ℤ)).kFlat ⊓ F.kFlatMap

variable [F.PreservesFlat] [PreservesColimitsOfShape ℤ F]

/-- The K-flat complexes whose image under `F` is K-flat form a left derivability structure on
`K(C)` for the quasi-isomorphisms: the functorial flat resolutions are such complexes. -/
instance isLeftDerivabilityStructure_kFlatInterKFlatMap :
    (HomotopyCategory.quasiIsoLocalizerMorphism
      F.kFlatInterKFlatMap).IsLeftDerivabilityStructure :=
  let Λ := (inferInstance : HasFunctorialFlatResolution C).some
  HomotopyCategory.isLeftDerivabilityStructure_quasiIsoLocalizerMorphism _
    Λ.reduced.resolutionNatTrans (fun _ ↦ inferInstance)
    (fun K ↦ ⟨(HomotopyCategory.kFlat_quotient_obj_iff _).2
      (Λ.reduced.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le K),
      F.kFlatMap_quotient_obj_resolutionFunctor_obj Λ.reduced K⟩)

end

section Comparison

variable (F : C ⥤ D) [F.Additive] [F.PreservesKFlatQuasiIso]

/-- The bifunctor `(K, M) ↦ LF K ⊗ᴸ LF M`, of type `D(C) ⥤ D(C) ⥤ D(D)`. -/
noncomputable abbrev derivedTensorLeftDerivedOfKFlat :
    DerivedCategory C ⥤ DerivedCategory C ⥤ DerivedCategory D :=
  (((whiskeringLeft₂ _).obj F.leftDerivedFunctor).obj F.leftDerivedFunctor).obj
    (curriedTensor _)

/-- The bifunctor `(K, M) ↦ LF(K ⊗ᴸ M)`, of type `D(C) ⥤ D(C) ⥤ D(D)`. -/
noncomputable abbrev leftDerivedDerivedTensorOfKFlat :
    DerivedCategory C ⥤ DerivedCategory C ⥤ DerivedCategory D :=
  (postcompose₂.obj F.leftDerivedFunctor).obj (curriedTensor _)

/-- The counit exhibiting `(K, M) ↦ LF K ⊗ᴸ LF M` as the total left derived functor of
`(A, B) ↦ F A ⊗ F B`: the counits of `LF` on both factors followed by the lax monoidal
structure of `Qh : K(D) ⥤ D(D)`. -/
noncomputable def derivedTensorLeftDerivedCounitOfKFlat :
    (((whiskeringLeft₂ _).obj (Qh (C := C))).obj Qh).obj (derivedTensorLeftDerivedOfKFlat F) ⟶
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
`(A, B) ↦ F(A ⊗ B)`: `LF(μ Qh)` followed by the counit of `LF`. -/
noncomputable def leftDerivedDerivedTensorCounitOfKFlat :
    (((whiskeringLeft₂ _).obj (Qh (C := C))).obj Qh).obj (leftDerivedDerivedTensorOfKFlat F) ⟶
      (postcompose₂.obj (F.mapHomotopyCategory (.up ℤ) ⋙ Qh)).obj (curriedTensor _) :=
  (postcompose₂.obj F.leftDerivedFunctor).map (LaxMonoidal.μNatTrans Qh) ≫
    (postcompose₂.map F.leftDerivedFunctorCounit).app (curriedTensor _)

omit [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [HasFunctorialFlatResolution D] in
/-- The counit of `LF` is an isomorphism on K-flat objects of `K(C)`. -/
lemma isIso_leftDerivedFunctorCounit_app_of_kFlat' (X : HomotopyCategory C (.up ℤ))
    (hX : (HomotopyCategory.quasiIso C (.up ℤ)).kFlat X) :
    IsIso (F.leftDerivedFunctorCounit.app X) := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  exact F.isIso_leftDerivedFunctorCounit_app_of_kFlat K
    ((HomotopyCategory.kFlat_quotient_obj_iff K).1 hX)

variable [F.PreservesFlat] [PreservesColimitsOfShape ℤ F]

/-- `(K, M) ↦ LF K ⊗ᴸ LF M` is the total left derived functor of `(A, B) ↦ F A ⊗ F B`. It is
computed on pairs `(K, M)` with `K` K-flat and `M`, `F M` K-flat. -/
instance isLeftDerivedFunctor₂_derivedTensorLeftDerivedOfKFlat :
    (derivedTensorLeftDerivedOfKFlat F).IsLeftDerivedFunctor₂
      (derivedTensorLeftDerivedCounitOfKFlat F)
      (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) := by
  refine LocalizerMorphism.isLeftDerivedFunctor₂_of_isLeftDerivabilityStructure
    (HomotopyCategory.quasiIso _ (.up ℤ)).localizerMorphismKFlat
    (HomotopyCategory.quasiIsoLocalizerMorphism F.kFlatInterKFlatMap) _ (fun X₁ X₂ ↦ ?_)
  have := isIso_μNatTrans_Qh_app_app_of_kFlat
    ((F.mapHomotopyCategory _).obj X₁.obj) _ X₂.property.2
  have h₁ := F.isIso_leftDerivedFunctorCounit_app_of_kFlat' X₁.obj X₁.property
  have h₂ := F.isIso_leftDerivedFunctorCounit_app_of_kFlat' X₂.obj X₂.property.1
  simp only [derivedTensorLeftDerivedCounitOfKFlat, NatTrans.comp_app]
  dsimp at this h₁ h₂ ⊢
  infer_instance

/-- `(K, M) ↦ LF(K ⊗ᴸ M)` is the total left derived functor of `(A, B) ↦ F(A ⊗ B)`. It is
computed on pairs of K-flat complexes. -/
instance isLeftDerivedFunctor₂_leftDerivedDerivedTensorOfKFlat :
    (leftDerivedDerivedTensorOfKFlat F).IsLeftDerivedFunctor₂
      (leftDerivedDerivedTensorCounitOfKFlat F)
      (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) := by
  refine LocalizerMorphism.isLeftDerivedFunctor₂_of_isLeftDerivabilityStructure
    (HomotopyCategory.quasiIso _ (.up ℤ)).localizerMorphismKFlat
    (HomotopyCategory.quasiIso _ (.up ℤ)).localizerMorphismKFlat _ (fun X₁ X₂ ↦ ?_)
  have := isIso_μNatTrans_Qh_app_app_of_kFlat X₁.obj _ X₂.property
  have := F.isIso_leftDerivedFunctorCounit_app_of_kFlat' (X₁.obj ⊗ X₂.obj)
    ((HomotopyCategory.quasiIso C (.up ℤ)).kFlat.prop_tensor X₁.property X₂.property)
  simp only [leftDerivedDerivedTensorCounitOfKFlat, NatTrans.comp_app]
  exact IsIso.comp_isIso'
    (Functor.map_isIso F.leftDerivedFunctor (((LaxMonoidal.μNatTrans Qh).app X₁.obj).app X₂.obj))
    this

variable [F.IsLeftAdjoint] [F.Monoidal]

/-- The comparison `LF(K ⊗ᴸ M) ⟶ LF K ⊗ᴸ LF M` of bifunctors `D(C) ⥤ D(C) ⥤ D(D)`, obtained by
deriving the comonoidal structure `δ` of `F`. -/
noncomputable def leftDerivedTensorComparisonOfKFlat :
    leftDerivedDerivedTensorOfKFlat F ⟶ derivedTensorLeftDerivedOfKFlat F :=
  leftDerived₂NatTrans _ (derivedTensorLeftDerivedCounitOfKFlat F)
    (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) _
    (leftDerivedDerivedTensorCounitOfKFlat F)
    (postcompose₂MapWhiskeringLeft₂ (OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) F) Qh)

/-- The comparison `LF(K ⊗ᴸ M) ⟶ LF K ⊗ᴸ LF M` is an isomorphism, `F` being strong
monoidal. -/
instance isIso_leftDerivedTensorComparisonOfKFlat :
    IsIso F.leftDerivedTensorComparisonOfKFlat := by
  dsimp only [leftDerivedTensorComparisonOfKFlat]
  infer_instance

end Comparison

end CategoryTheory.Functor
