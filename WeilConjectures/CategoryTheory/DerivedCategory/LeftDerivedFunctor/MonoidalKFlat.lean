/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal

/-!
# The tensor comparison of the left derived functor of a right exact monoidal functor

Let `F : C ⥤ D` be a strong monoidal functor between monoidal Grothendieck abelian categories
with functorial flat resolutions, which preserves flat objects, is a left adjoint and sends
quasi-isomorphisms between K-flat complexes to quasi-isomorphisms
(`CategoryTheory.Functor.PreservesKFlatQuasiIso`), for instance extension of scalars of sheaves
of modules along a ring morphism. As for exact functors
(`WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal`), the bifunctors
`(K, M) ↦ LF(K ⊗ᴸ M)` and `(K, M) ↦ LF K ⊗ᴸ LF M` are the total left derived functors of
`(A, B) ↦ F(A ⊗ B)` and `(A, B) ↦ F A ⊗ F B`, and deriving the comonoidal structure `δ` of `F`
gives a natural isomorphism `LF(K ⊗ᴸ M) ≅ LF K ⊗ᴸ LF M`. Exactness of `F` is not needed: the
first bifunctor is computed on pairs of K-flat complexes, on which the counit of `LF` is an
isomorphism, and the second one on pairs `(K, M)` with `K`, `M` and `F M` K-flat.

## Main definitions

- `CategoryTheory.Functor.leftDerivedTensorComparisonOfKFlat F`: the comparison
  `LF(K ⊗ᴸ M) ⟶ LF K ⊗ᴸ LF M`, an isomorphism.
- `CategoryTheory.Functor.leftDerivedTensorIsoOfKFlat F K`: for fixed `K`, the natural
  isomorphism `LF(K ⊗ᴸ -) ≅ LF K ⊗ᴸ LF(-)`.
-/

@[expose] public section

universe u u₁ u₂

open CategoryTheory Abelian Limits MonoidalCategory DerivedCategory

open scoped CategoryTheory.Functor

namespace HomotopyCategory

variable {C : Type u₁} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]

/-- The tensor product of two K-flat complexes is K-flat. -/
lemma kFlat_tensorObj {K L : HomotopyCategory C (.up ℤ)}
    (hK : (HomotopyCategory.quasiIso C (.up ℤ)).kFlat K)
    (hL : (HomotopyCategory.quasiIso C (.up ℤ)).kFlat L) :
    (HomotopyCategory.quasiIso C (.up ℤ)).kFlat (K ⊗ L) := by
  rw [kFlat_iff_preserves_acyclic] at hK hL ⊢
  intro Z hZ
  exact ⟨(subcategoryAcyclic C).prop_of_iso (α_ K L Z).symm (hK _ (hL Z hZ).1).1,
    (subcategoryAcyclic C).prop_of_iso (α_ Z K L) (hL _ (hK Z hZ).2).2⟩

end HomotopyCategory

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasFunctorialFlatResolution C]
  {D : Type u₂} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [HasFunctorialFlatResolution D]

variable (F : C ⥤ D) [F.Additive] [F.PreservesKFlatQuasiIso]

omit [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [HasFunctorialFlatResolution D] in
/-- On a K-flat complex, the counit of the total left derived functor of `F` is an
isomorphism. -/
lemma isIso_leftDerivedFunctorCounit_app_of_kFlat' (X : HomotopyCategory C (.up ℤ))
    (hX : (HomotopyCategory.quasiIso C (.up ℤ)).kFlat X) :
    IsIso (F.leftDerivedFunctorCounit.app X) :=
  F.derives_kFlat.isIso_of_isLeftDerivedFunctor F.leftDerivedFunctorCounit ⟨X, hX⟩

/-- The bifunctor `(K, M) ↦ LF K ⊗ᴸ LF M`, of type `D(C) ⥤ D(C) ⥤ D(D)`, for a functor `F`
preserving K-flat quasi-isomorphisms. -/
noncomputable abbrev derivedTensorLeftDerivedOfKFlat :
    DerivedCategory C ⥤ DerivedCategory C ⥤ DerivedCategory D :=
  (((whiskeringLeft₂ _).obj F.leftDerivedFunctor).obj F.leftDerivedFunctor).obj
    (curriedTensor _)

/-- The bifunctor `(K, M) ↦ LF(K ⊗ᴸ M)`, of type `D(C) ⥤ D(C) ⥤ D(D)`, for a functor `F`
preserving K-flat quasi-isomorphisms. -/
noncomputable abbrev leftDerivedDerivedTensorOfKFlat :
    DerivedCategory C ⥤ DerivedCategory C ⥤ DerivedCategory D :=
  (postcompose₂.obj F.leftDerivedFunctor).obj (curriedTensor _)

/-- The counit exhibiting `(K, M) ↦ LF K ⊗ᴸ LF M` as the total left derived functor of
`(A, B) ↦ F A ⊗ F B`: on `K, M` in `K(C)` it is the composite of the counits of `LF` on both
factors and of the lax monoidal structure of `Qh : K(D) ⥤ D(D)`. -/
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
`(A, B) ↦ F(A ⊗ B)`: on `K, M` in `K(C)` it is `LF(μ Qh)` followed by the counit of `LF`. -/
noncomputable def leftDerivedDerivedTensorCounitOfKFlat :
    (((whiskeringLeft₂ _).obj (Qh (C := C))).obj Qh).obj (leftDerivedDerivedTensorOfKFlat F) ⟶
      (postcompose₂.obj (F.mapHomotopyCategory (.up ℤ) ⋙ Qh)).obj (curriedTensor _) :=
  (postcompose₂.obj F.leftDerivedFunctor).map (LaxMonoidal.μNatTrans Qh) ≫
    (postcompose₂.map F.leftDerivedFunctorCounit).app (curriedTensor _)

/-- The K-flat complexes in `K(C)` whose image under `F : C ⥤ D` is K-flat. -/
abbrev kFlatInfKFlatMap : ObjectProperty (HomotopyCategory C (.up ℤ)) :=
  (HomotopyCategory.quasiIso C (.up ℤ)).kFlat ⊓ F.kFlatMap

variable [F.PreservesFlat] [F.IsLeftAdjoint]

/-- The K-flat complexes whose image under `F` is K-flat form a left derivability structure on
`K(C)` for the quasi-isomorphisms: they contain the functorial flat resolutions. -/
instance isLeftDerivabilityStructure_kFlatInfKFlatMap :
    (HomotopyCategory.quasiIsoLocalizerMorphism F.kFlatInfKFlatMap).IsLeftDerivabilityStructure :=
  let Λ := (inferInstance : HasFunctorialFlatResolution C).some
  HomotopyCategory.isLeftDerivabilityStructure_quasiIsoLocalizerMorphism _
    Λ.reduced.resolutionNatTrans (fun _ ↦ inferInstance)
    (fun K ↦ ⟨(HomotopyCategory.kFlat_quotient_obj_iff _).2
      (Λ.reduced.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le K),
      F.kFlatMap_quotient_obj_resolutionFunctor_obj Λ.reduced K⟩)

/-- `(K, M) ↦ LF K ⊗ᴸ LF M` is the total left derived functor of `(A, B) ↦ F A ⊗ F B`. It is
computed on pairs `(K, M)` with `K` K-flat, and `M` and `F M` K-flat. -/
instance isLeftDerivedFunctor₂_derivedTensorLeftDerivedOfKFlat :
    (derivedTensorLeftDerivedOfKFlat F).IsLeftDerivedFunctor₂
      (derivedTensorLeftDerivedCounitOfKFlat F)
      (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) := by
  refine LocalizerMorphism.isLeftDerivedFunctor₂_of_isLeftDerivabilityStructure
    (HomotopyCategory.quasiIso _ (.up ℤ)).localizerMorphismKFlat
    (HomotopyCategory.quasiIsoLocalizerMorphism F.kFlatInfKFlatMap) _ (fun X₁ X₂ ↦ ?_)
  have hμ := isIso_μNatTrans_Qh_app_app_of_kFlat
    ((F.mapHomotopyCategory _).obj X₁.obj) _ X₂.property.2
  have := F.isIso_leftDerivedFunctorCounit_app_of_kFlat' X₁.obj X₁.property
  have := F.isIso_leftDerivedFunctorCounit_app_of_kFlat' X₂.obj X₂.property.1
  simp only [derivedTensorLeftDerivedCounitOfKFlat, NatTrans.comp_app]
  exact IsIso.comp_isIso'
    (inferInstanceAs (IsIso (((curriedTensor _).map (F.leftDerivedFunctorCounit.app X₁.obj)).app
      (L(F).obj (Qh.obj X₂.obj)))))
    (IsIso.comp_isIso' (inferInstanceAs (IsIso (((curriedTensor _).obj
      (Qh.obj ((F.mapHomotopyCategory _).obj X₁.obj))).map
        (F.leftDerivedFunctorCounit.app X₂.obj))))
      hμ)

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
    (HomotopyCategory.kFlat_tensorObj X₁.property X₂.property)
  simp only [leftDerivedDerivedTensorCounitOfKFlat, NatTrans.comp_app]
  exact IsIso.comp_isIso'
    (Functor.map_isIso F.leftDerivedFunctor (((LaxMonoidal.μNatTrans Qh).app X₁.obj).app X₂.obj))
    (inferInstanceAs (IsIso (F.leftDerivedFunctorCounit.app (X₁.obj ⊗ X₂.obj))))

variable [F.Monoidal]

/-- The comparison `LF(K ⊗ᴸ M) ⟶ LF K ⊗ᴸ LF M` of bifunctors `D(C) ⥤ D(C) ⥤ D(D)`, obtained by
deriving the comonoidal structure `δ` of `F`, for a functor `F` preserving K-flat
quasi-isomorphisms. -/
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

/-- For a fixed `K`, the natural isomorphism `LF(K ⊗ᴸ M) ≅ LF K ⊗ᴸ LF M` in `M`. -/
noncomputable def leftDerivedTensorIsoOfKFlat (K : DerivedCategory C) :
    tensorLeft K ⋙ F.leftDerivedFunctor ≅ F.leftDerivedFunctor ⋙ tensorLeft (L(F).obj K) :=
  asIso (F.leftDerivedTensorComparisonOfKFlat.app K)

end CategoryTheory.Functor
