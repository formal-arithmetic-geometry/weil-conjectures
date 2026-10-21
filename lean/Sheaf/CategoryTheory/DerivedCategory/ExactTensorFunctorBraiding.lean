/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.CategoryTheory.DerivedTensorComparison
public import Sheaf.Algebra.Homology.PreservesTotalTensorKFlatQuasiIso
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory

import Mathlib.CategoryTheory.Adjunction.Limits
import Sheaf.CategoryTheory.DerivedCategory.KFlatDerivability

/-!
# Exact tensor functors preserve the native derived braiding

Source: Stacks Project, `sites-cohomology.tex`, Tags 0FPQ and 0FPT, and the
cross-functor calculation in the DAG proof
(blueprint: lem-sfb-exact-tensor-functor-derived-braiding).

The K-flat model isomorphism in the node is the inverse of the native localization
counit `Functor.LaxMonoidal.μ DerivedCategory.Q`. The hypothesis `hnormalized` writes
the same square after composing with the source and target counits. Those counits
are invertible on K-flat pairs. This avoids choosing another model comparison.
The two occurrences of `DerivedMonoidal.braiding'` are the independently constructed
native braidings, descended from the Koszul braidings of the homotopy categories.
-/

@[expose] public section

set_option autoImplicit false

universe uC vC wC uD vD wD

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CategoryTheory.Functor

private theorem bifunctor_component_eq_of_iso
    {A B : Type*} [Category A] [Category B] {H J : A ⥤ A ⥤ B}
    (γ δ : H ⟶ J) {P Q K L : A} (e : P ≅ K) (f : Q ≅ L)
    (h : (γ.app P).app Q = (δ.app P).app Q) :
    (γ.app K).app L = (δ.app K).app L := by
  have hQ : (γ.app K).app Q = (δ.app K).app Q := by
    apply (cancel_epi ((H.map e.hom).app Q)).mp
    rw [NatTrans.naturality_app, NatTrans.naturality_app, h]
  apply (cancel_epi ((H.obj K).map f.hom)).mp
  rw [(γ.app K).naturality, (δ.app K).naturality, hQ]

private theorem native_braiding_naturality
    {A B : Type*} [Category A] [Category B] [MonoidalCategory A] [BraidedCategory A]
    (L : A ⥤ B) (W : MorphismProperty A) [L.IsLocalization W] [W.ContainsIdentities]
    [L.HasDerivedMonoidalCategory W]
    {X X' Y Y' : DerivedMonoidal L W} (f : X ⟶ X') (g : Y ⟶ Y') :
    (f ⊗ₘ g) ≫ (DerivedMonoidal.braiding' L W X' Y').hom =
      (DerivedMonoidal.braiding' L W X Y).hom ≫ (g ⊗ₘ f) := by
  rw [tensorHom_def, Category.assoc, DerivedMonoidal.braiding_naturality_right,
    ← Category.assoc, DerivedMonoidal.braiding_naturality_left,
    Category.assoc, ← tensorHom_def']

private theorem complex_braiding_square
    {C : Type uC} [Category.{vC} C] [Abelian C] [IsGrothendieckAbelian.{vC} C]
    [MonoidalCategory C] [SymmetricCategory C] [MonoidalPreadditive C] [MonoidalClosed C]
    {D : Type uD} [Category.{vD} D] [Abelian D] [IsGrothendieckAbelian.{vD} D]
    [MonoidalCategory D] [SymmetricCategory D] [MonoidalPreadditive D] [MonoidalClosed D]
    (F : C ⥤ D) [F.Additive] [F.IsLeftAdjoint] (M : F.CoreMonoidal)
    (τ : ∀ P Q : CochainComplex C ℤ,
      (F.mapHomologicalComplex (.up ℤ)).obj (P ⊗ Q) ⟶
        (F.mapHomologicalComplex (.up ℤ)).obj P ⊗
          (F.mapHomologicalComplex (.up ℤ)).obj Q)
    (hτ : ∀ (P Q : CochainComplex C ℤ) (p q n : ℤ) (h : p + q = n),
      F.map (HomologicalComplex.ιTensorObj P Q p q n h) ≫ (τ P Q).f n =
        (M.μIso (P.X p) (Q.X q)).inv ≫ HomologicalComplex.ιTensorObj
          ((F.mapHomologicalComplex (.up ℤ)).obj P)
          ((F.mapHomologicalComplex (.up ℤ)).obj Q) p q n h)
    (hbraided : ∀ A B : C,
      F.map (β_ A B).hom ≫ (M.μIso B A).inv =
        (M.μIso A B).inv ≫ (β_ (F.obj A) (F.obj B)).hom)
    (P Q : CochainComplex C ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).map (β_ P Q).hom ≫ τ Q P =
      τ P Q ≫ (β_ ((F.mapHomologicalComplex (.up ℤ)).obj P)
        ((F.mapHomologicalComplex (.up ℤ)).obj Q)).hom := by
  apply HomologicalComplex.hom_ext
  intro n
  change F.map ((β_ P Q).hom.f n) ≫ (τ Q P).f n = _
  apply HomologicalComplex.mapBifunctor.hom_ext_of_map F
  intro p q h
  change F.map (HomologicalComplex.ιTensorObj P Q p q n h) ≫ _ =
    F.map (HomologicalComplex.ιTensorObj P Q p q n h) ≫ _
  rw [← F.map_comp_assoc]
  change F.map (HomologicalComplex.ιTensorObj P Q p q n h ≫
    (CochainComplex.Monoidal.braiding P Q).hom.f n) ≫ _ = _
  rw [CochainComplex.Monoidal.ι_braiding_hom, F.map_zsmul, F.map_comp,
    Preadditive.zsmul_comp, Category.assoc, hτ]
  simp only [HomologicalComplex.comp_f]
  rw [reassoc_of% hτ P Q p q n h]
  change _ = (M.μIso (P.X p) (Q.X q)).inv ≫
    (HomologicalComplex.ιTensorObj
      ((F.mapHomologicalComplex (.up ℤ)).obj P)
      ((F.mapHomologicalComplex (.up ℤ)).obj Q) p q n h ≫
      (CochainComplex.Monoidal.braiding
        ((F.mapHomologicalComplex (.up ℤ)).obj P)
        ((F.mapHomologicalComplex (.up ℤ)).obj Q)).hom.f n)
  rw [CochainComplex.Monoidal.ι_braiding_hom, Preadditive.comp_zsmul]
  erw [reassoc_of% hbraided]
  rfl

private theorem tensorLocalization_isIso
    {C : Type uC} [Category.{vC} C] [Abelian C] [IsGrothendieckAbelian.{vC} C]
    [HasDerivedCategory.{wC} C] [MonoidalCategory C] [SymmetricCategory C]
    [MonoidalPreadditive C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    (P Q : CochainComplex C ℤ) (hQ : Q.IsKFlatForTotalTensor) :
    IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) := by
  have : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Qh
      ((HomotopyCategory.quotient C (.up ℤ)).obj P)
      ((HomotopyCategory.quotient C (.up ℤ)).obj Q)) :=
    DerivedMonoidal.isIso_counit_app_app_of_kFlat_right DerivedCategory.Qh
      (HomotopyCategory.quasiIso C (.up ℤ)) _ _
      ((HomotopyCategory.kFlat_quotient_obj_iff Q).2 hQ)
  change IsIso ((_ ⊗ₘ _) ≫
    (Functor.LaxMonoidal.μ DerivedCategory.Qh _ _ ≫ DerivedCategory.Qh.map _) ≫ _)
  infer_instance

private theorem native_braiding_Q
    {C : Type uC} [Category.{vC} C] [Abelian C] [IsGrothendieckAbelian.{vC} C]
    [HasDerivedCategory.{wC} C] [MonoidalCategory C] [SymmetricCategory C]
    [MonoidalPreadditive C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    (P Q : CochainComplex C ℤ) :
    (DerivedMonoidal.braiding' DerivedCategory.Qh
      (HomotopyCategory.quasiIso C (.up ℤ))
      (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q Q P =
      Functor.LaxMonoidal.μ DerivedCategory.Q P Q ≫
        DerivedCategory.Q.map (β_ P Q).hom := by
  let e := DerivedCategory.quotientCompQhIso C
  change _ ≫ ((e.inv.app Q ⊗ₘ e.inv.app P) ≫
      (Functor.LaxMonoidal.μ DerivedCategory.Qh _ _ ≫ DerivedCategory.Qh.map _) ≫
        e.hom.app _) =
    ((e.inv.app P ⊗ₘ e.inv.app Q) ≫
      (Functor.LaxMonoidal.μ DerivedCategory.Qh _ _ ≫ DerivedCategory.Qh.map _) ≫
        e.hom.app _) ≫ _
  rw [← Category.assoc, ← native_braiding_naturality]
  simp only [Category.assoc]
  erw [DerivedMonoidal.braiding_hom_μ_assoc]
  change _ ≫ _ ≫ DerivedCategory.Qh.map
      (HomotopyCategory.braiding _ _).hom ≫ DerivedCategory.Qh.map (𝟙 _) ≫ _ =
    _ ≫ _ ≫ DerivedCategory.Qh.map (𝟙 _) ≫ _ ≫ _
  simp only [Functor.map_id, Category.id_comp]
  erw [e.hom.naturality]
  rfl


/-- The prescribed normalized exact tensor comparison intertwines the native braidings.
Source: Stacks Project, Tags 0FPQ (lemma-symmetric-monoidal-cat-complexes) and
0FPT (lemma-symmetric-monoidal-derived); agent extraction of the cross-functor square
(blueprint: lem-sfb-exact-tensor-functor-derived-braiding).

Proof: (1) Precompose the two complex-level braiding composites with each image of a
bidegree coproduct inclusion. The defining equation `hτ` reduces them to the ordinary
braiding square `hbraided`, multiplied by the same Koszul sign. Additivity moves the
sign through F, and the left-adjoint hypothesis gives coproduct uniqueness.
(2) The native braiding normalization for the homotopy localization transports to
complexes along `quotientCompQhIso`, using naturality of the native derived braiding.
(3) For K-flat P,Q, postcompose the required square with the tensor of the two
factorization isomorphisms followed by the target localization counit. This is an
isomorphism because F preserves K-flat complexes. Source braiding normalization,
`hnormalized` at Q,P, and naturality of the factorization identify the first side
with the image of the first complex composite. Target braiding naturality,
`hnormalized` at P,Q, and target normalization identify the second side with the
image of the second complex composite. Step (1) identifies these; cancel the target
isomorphism. No invertibility of t is used.
(4) Closedness and symmetry give colimit preservation by tensoring on either side.
Apply `kFlat_derivability` to the given functorial flat resolution to obtain a
K-flat replacement functor with a natural quasi-isomorphism. Every derived object
is isomorphic to the localization of such a replacement. Regard the two sides as
natural transformations of bifunctors and transport their equality at K-flat
representatives along these isomorphisms, using naturality in each variable. -/
theorem exactTensorFunctor_derived_braiding
    {C : Type uC} [Category.{vC} C] [Abelian C] [IsGrothendieckAbelian.{vC} C]
    [HasDerivedCategory.{wC} C] [MonoidalCategory C] [SymmetricCategory C]
    [MonoidalPreadditive C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    {D : Type uD} [Category.{vD} D] [Abelian D] [IsGrothendieckAbelian.{vD} D]
    [HasDerivedCategory.{wD} D] [MonoidalCategory D] [SymmetricCategory D]
    [MonoidalPreadditive D] [MonoidalClosed D] [Abelian.HasFunctorialFlatResolution D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.IsLeftAdjoint] [F.PreservesFlat] (M : F.CoreMonoidal)
    (hKFlat : ∀ P : CochainComplex C ℤ, P.IsKFlatForTotalTensor →
      CochainComplex.IsKFlatForTotalTensor ((F.mapHomologicalComplex (.up ℤ)).obj P))
    (τ : (Functor.postcompose₂.obj (F.mapHomologicalComplex (.up ℤ))).obj
        (curriedTensor (CochainComplex C ℤ)) ≅
      (((Functor.whiskeringLeft₂ _).obj (F.mapHomologicalComplex (.up ℤ))).obj
        (F.mapHomologicalComplex (.up ℤ))).obj (curriedTensor (CochainComplex D ℤ)))
    (hτ : ∀ (P Q : CochainComplex C ℤ) (p q n : ℤ) (h : p + q = n),
      F.map (HomologicalComplex.ιTensorObj P Q p q n h) ≫
          ((τ.hom.app P).app Q).f n =
        (M.μIso (P.X p) (Q.X q)).inv ≫ HomologicalComplex.ιTensorObj
          ((F.mapHomologicalComplex (.up ℤ)).obj P)
          ((F.mapHomologicalComplex (.up ℤ)).obj Q) p q n h)
    (t : (Functor.postcompose₂.obj F.mapDerivedCategory).obj
        (curriedTensor (DerivedCategory C)) ⟶
      (((Functor.whiskeringLeft₂ _).obj F.mapDerivedCategory).obj
        F.mapDerivedCategory).obj (curriedTensor (DerivedCategory D)))
    (hnormalized : ∀ (P Q : CochainComplex C ℤ),
      P.IsKFlatForTotalTensor → Q.IsKFlatForTotalTensor →
      F.mapDerivedCategory.map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
          F.mapDerivedCategoryFactors.hom.app (P ⊗ Q) ≫
          DerivedCategory.Q.map ((τ.hom.app P).app Q) =
        (t.app (DerivedCategory.Q.obj P)).app (DerivedCategory.Q.obj Q) ≫
          (F.mapDerivedCategoryFactors.hom.app P ⊗ₘ
            F.mapDerivedCategoryFactors.hom.app Q) ≫
          Functor.LaxMonoidal.μ DerivedCategory.Q
            ((F.mapHomologicalComplex (.up ℤ)).obj P)
            ((F.mapHomologicalComplex (.up ℤ)).obj Q))
    (hbraided : ∀ A B : C,
      F.map (β_ A B).hom ≫ (M.μIso B A).inv =
        (M.μIso A B).inv ≫ (β_ (F.obj A) (F.obj B)).hom)
    (K L : DerivedCategory C) :
    F.mapDerivedCategory.map
        (DerivedMonoidal.braiding' DerivedCategory.Qh
          (HomotopyCategory.quasiIso C (.up ℤ)) K L).hom ≫ (t.app L).app K =
      (t.app K).app L ≫
        (DerivedMonoidal.braiding' DerivedCategory.Qh
          (HomotopyCategory.quasiIso D (.up ℤ))
          (F.mapDerivedCategory.obj K) (F.mapDerivedCategory.obj L)).hom := by
  have hcomplex := complex_braiding_square F M (fun P Q ↦ (τ.hom.app P).app Q)
    hτ hbraided
  have hmodels (P Q : CochainComplex C ℤ)
      (hP : P.IsKFlatForTotalTensor) (hQ : Q.IsKFlatForTotalTensor) :
      F.mapDerivedCategory.map
          (DerivedMonoidal.braiding' DerivedCategory.Qh
            (HomotopyCategory.quasiIso C (.up ℤ))
            (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom ≫
            (t.app (DerivedCategory.Q.obj Q)).app (DerivedCategory.Q.obj P) =
        (t.app (DerivedCategory.Q.obj P)).app (DerivedCategory.Q.obj Q) ≫
          (DerivedMonoidal.braiding' DerivedCategory.Qh
            (HomotopyCategory.quasiIso D (.up ℤ))
            (F.mapDerivedCategory.obj (DerivedCategory.Q.obj P))
            (F.mapDerivedCategory.obj (DerivedCategory.Q.obj Q))).hom := by
    have := tensorLocalization_isIso
      ((F.mapHomologicalComplex (.up ℤ)).obj Q)
      ((F.mapHomologicalComplex (.up ℤ)).obj P) (hKFlat P hP)
    apply (cancel_mono ((F.mapDerivedCategoryFactors.hom.app Q ⊗ₘ
      F.mapDerivedCategoryFactors.hom.app P) ≫ Functor.LaxMonoidal.μ
        DerivedCategory.Q ((F.mapHomologicalComplex (.up ℤ)).obj Q)
          ((F.mapHomologicalComplex (.up ℤ)).obj P))).mp
    have hnPQ := hnormalized P Q hP hQ
    have hnQP := hnormalized Q P hQ hP
    have hbC := F.mapDerivedCategory.congr_map (native_braiding_Q P Q)
    have hbD := native_braiding_Q
      ((F.mapHomologicalComplex (.up ℤ)).obj P)
      ((F.mapHomologicalComplex (.up ℤ)).obj Q)
    have hnat := native_braiding_naturality DerivedCategory.Qh
      (HomotopyCategory.quasiIso D (.up ℤ))
      (F.mapDerivedCategoryFactors.hom.app P) (F.mapDerivedCategoryFactors.hom.app Q)
    have hfac := F.mapDerivedCategoryFactors.hom.naturality (β_ P Q).hom
    have hcmp := DerivedCategory.Q.congr_map (hcomplex P Q)
    simp only [Functor.comp_map, Functor.map_comp, Category.assoc]
      at hbC hfac hcmp hnPQ hnQP ⊢
    rw [← hnQP, reassoc_of% hbC, reassoc_of% hfac, hcmp]
    rw [← reassoc_of% hnat, hbD, ← reassoc_of% hnPQ]
  let γ := whiskerRight
      ((flipFunctor _ _ _).map (DerivedMonoidal.braidingNatTrans DerivedCategory.Qh
        (HomotopyCategory.quasiIso C (.up ℤ))))
      ((whiskeringRight _ _ _).obj F.mapDerivedCategory) ≫
    (flipFunctor _ _ _).map t
  let δ := t ≫ (((Functor.whiskeringLeft₂ _).obj F.mapDerivedCategory).obj
      F.mapDerivedCategory).map
        ((flipFunctor _ _ _).map (DerivedMonoidal.braidingNatTrans DerivedCategory.Qh
          (HomotopyCategory.quasiIso D (.up ℤ))))
  have (X : C) : PreservesColimits (tensorRight X) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight X)
  let Λ := (inferInstance : Abelian.HasFunctorialFlatResolution C).some
  obtain ⟨R, r, hR, hr, _⟩ := kFlat_derivability
    (Λ.F ⋙ ObjectProperty.flat.ι) Λ.π
    (fun X ↦ (Λ.F.obj X).property) (fun X ↦ inferInstance)
  have hrep (X : DerivedCategory C) :
      ∃ P : CochainComplex C ℤ, P.IsKFlatForTotalTensor ∧
        Nonempty (DerivedCategory.Q.obj P ≅ X) := by
    let P := DerivedCategory.Q.objPreimage X
    have : QuasiIso (r.app P) := hr P
    exact ⟨R.obj P, hR P, ⟨asIso (DerivedCategory.Q.map (r.app P)) ≪≫
      DerivedCategory.Q.objObjPreimageIso X⟩⟩
  obtain ⟨P, hP, ⟨e⟩⟩ := hrep K
  obtain ⟨Q, hQ, ⟨f⟩⟩ := hrep L
  exact bifunctor_component_eq_of_iso γ δ e f (hmodels P Q hP hQ)

end CategoryTheory.Functor
