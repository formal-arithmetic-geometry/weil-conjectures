/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NativeWeilInduction.NativeWeilInductionComparisonData
import WeilConjectures.AlgebraicGeometry.NativeWeilInduction.NativeWeilProperNormalization
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.DerivedExactCompositionComparison

/-! # Compatibility of native compact supports with localized Weil structures

Source: blueprint `lem-fix-weil-operations`, paragraphs 1--2, and the native
comparison proof, step 6. (blueprint: lem-sf-native-weil-comparison-structure)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor

attribute [instance] AlgebraicGeometry.Compactification.over

namespace AlgebraicGeometry.NativeWeilInduction

section Compatibility

universe v w

variable {C : Type u} {D : Type v} [Category.{w} C] [Category.{w} D]
  [Abelian C] [Abelian D] [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]

private def localizedStructure (P : C ⥤ C) [P.Additive] [P.IsEquivalence]
    [HasDerivedCategory.{w} (IsoAlgebra P)] :
    (IsoAlgebra.forget P).mapDerivedCategory ⋙ P.mapDerivedCategory ≅
      (IsoAlgebra.forget P).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (IsoAlgebra.strNatIso P)

private theorem structure_fac (P : C ⥤ C) [P.Additive] [P.IsEquivalence]
    [HasDerivedCategory.{w} (IsoAlgebra P)]
    (J : HomotopyCategory (IsoAlgebra P) (.up ℤ)) :
    (localizedStructure P).hom.app (_root_.DerivedCategory.Qh.obj J) ≫
        (IsoAlgebra.forget P).mapDerivedCategoryFactorsh.hom.app J =
      P.mapDerivedCategory.map
          ((IsoAlgebra.forget P).mapDerivedCategoryFactorsh.hom.app J) ≫
        P.mapDerivedCategoryFactorsh.hom.app
          (((IsoAlgebra.forget P).mapHomotopyCategory (.up ℤ)).obj J) ≫
        _root_.DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory (IsoAlgebra.strNatIso P).hom (.up ℤ)).app J) := by
  dsimp only [localizedStructure, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  rw [Category.assoc, Functor.mapDerivedCategoryNatIso_fach]
  rw [← Functor.mapDerivedCategoryCompIso_hom_app_factorsh]
  erw [Category.assoc, Iso.inv_hom_id_app_assoc]
  exact Category.assoc _ _ _

private theorem exactSquare_fac
    {A B E : Type*} [Category.{w} A] [Category.{w} B] [Category.{w} E]
    [Abelian A] [Abelian B] [Abelian E]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B] [HasDerivedCategory.{w} E]
    (F : A ⥤ C) (G : C ⥤ E) (H : A ⥤ B) (I : B ⥤ E)
    [F.Additive] [G.Additive] [H.Additive] [I.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    (e : F ⋙ G ≅ H ⋙ I) (J : HomotopyCategory A (.up ℤ)) :
    (Functor.mapDerivedCategorySquareIso e).hom.app (_root_.DerivedCategory.Qh.obj J) ≫
        I.mapDerivedCategory.map (H.mapDerivedCategoryFactorsh.hom.app J) ≫
        I.mapDerivedCategoryFactorsh.hom.app ((H.mapHomotopyCategory (.up ℤ)).obj J) =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app J) ≫
        G.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj J) ≫
        _root_.DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app J) := by
  dsimp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app]
  simp only [Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factorsh,
    Functor.mapDerivedCategoryNatIso_fach]
  rw [← Functor.mapDerivedCategoryCompIso_hom_app_factorsh F G J]
  erw [Category.assoc, Iso.inv_hom_id_app_assoc]
  exact Category.assoc _ _ _

private theorem rightExchange_unit
    (P : C ⥤ C) (Q : D ⥤ D) [P.Additive] [Q.Additive]
    [P.IsEquivalence] [Q.IsEquivalence] (L : C ⥤ D) [L.Additive]
    [Abelian.HasKInjectiveResolutions C] (e : L ⋙ Q ≅ P ⋙ L)
    (J : HomotopyCategory C (.up ℤ)) :
    Q.mapDerivedCategory.map (L.rightDerivedFunctorUnit.app J) ≫
        (rightExchange P Q L e).hom.app (_root_.DerivedCategory.Qh.obj J) ≫
        L.rightDerivedFunctor.map (P.mapDerivedCategoryFactorsh.hom.app J) =
      Q.mapDerivedCategoryFactorsh.hom.app ((L.mapHomotopyCategory (.up ℤ)).obj J) ≫
        _root_.DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app J) ≫
        L.rightDerivedFunctorUnit.app ((P.mapHomotopyCategory (.up ℤ)).obj J) := by
  let a := Functor.rightDerivedFunctorCompMapDerivedCategoryIso L Q
  have ha := Functor.rightDerivedFunctorCompMapDerivedCategoryIso_hom_fac L Q J
  rw [Functor.rightDerivedFunctorCompMapDerivedCategoryUnit_app'] at ha
  have ha' : Q.mapDerivedCategory.map (L.rightDerivedFunctorUnit.app J) ≫
      a.inv.app (_root_.DerivedCategory.Qh.obj J) =
      Q.mapDerivedCategoryFactorsh.hom.app ((L.mapHomotopyCategory (.up ℤ)).obj J) ≫
        (L ⋙ Q).rightDerivedFunctorUnit.app J := by
    rw [← cancel_mono (a.hom.app (_root_.DerivedCategory.Qh.obj J))]
    simp only [Category.assoc, Iso.inv_hom_id_app]
    rw [ha]
    simp only [Iso.hom_inv_id_app_assoc]
    exact Category.comp_id _
  dsimp only [rightExchange, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app]
  rw [← Category.assoc, ← Category.assoc, ← Category.assoc, ha']
  simp only [Category.assoc]
  have hb := Functor.rightDerivedNatTrans_app
    (L ⋙ Q).rightDerivedFunctor (P ⋙ L).rightDerivedFunctor
    (L ⋙ Q).rightDerivedFunctorUnit (P ⋙ L).rightDerivedFunctorUnit
    (HomotopyCategory.quasiIso C (.up ℤ))
    (Functor.whiskerRight (NatTrans.mapHomotopyCategory e.hom (.up ℤ))
      _root_.DerivedCategory.Qh) J
  change (L ⋙ Q).rightDerivedFunctorUnit.app J ≫
      (Functor.rightDerivedFunctorNatIso e).hom.app (_root_.DerivedCategory.Qh.obj J) = _ at hb
  dsimp only [Functor.whiskerRight_app] at hb
  rw [reassoc_of% hb]
  have hc : (P ⋙ L).rightDerivedFunctorUnit.app J ≫
      (Functor.rightDerivedFunctorCompIso P L).hom.app
        (_root_.DerivedCategory.Qh.obj J) =
      (Functor.rightDerivedFunctorCompUnit P L).app J := by
    simp [Functor.rightDerivedFunctorCompIso]
  rw [reassoc_of% hc]
  have hunit : (Functor.rightDerivedFunctorCompUnit P L).app J =
      L.rightDerivedFunctorUnit.app ((P.mapHomotopyCategory (.up ℤ)).obj J) ≫
        L.rightDerivedFunctor.map (P.rightDerivedFunctorUnit.app J) := by
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective J
    simp only [Functor.rightDerivedFunctorCompUnit, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Category.id_comp, Category.comp_id]
    have hh : (Functor.mapHomotopyCategoryCompIso (Iso.refl (P ⋙ L)) (.up ℤ)).inv.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj K) = 𝟙 _ := rfl
    erw [hh, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [hunit]
  simp only [Category.assoc]
  rw [← L.rightDerivedFunctor.map_comp, ← L.rightDerivedFunctor.map_comp]
  have hd := congr_app P.rightDerivedFunctorIsoMapDerivedCategory_hom_fac J
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hd
  have hcancel : P.rightDerivedFunctorUnit.app J ≫
      P.rightDerivedFunctorIsoMapDerivedCategory.hom.app (_root_.DerivedCategory.Qh.obj J) ≫
        P.mapDerivedCategoryFactorsh.hom.app J = 𝟙 _ := by
    rw [← Category.assoc, hd, Iso.inv_hom_id_app]
  erw [hcancel, CategoryTheory.Functor.map_id, Category.comp_id]

private theorem model_structure
    (P : C ⥤ C) (Q : D ⥤ D) [P.Additive] [Q.Additive]
    [P.IsEquivalence] [Q.IsEquivalence] (L : C ⥤ D) [L.Additive]
    [HasDerivedCategory.{w} (IsoAlgebra P)] [HasDerivedCategory.{w} (IsoAlgebra Q)]
    (e : L ⋙ Q ≅ P ⋙ L)
    (W : _root_.DerivedCategory (IsoAlgebra P) ⥤ _root_.DerivedCategory (IsoAlgebra Q))
    (F : _root_.DerivedCategory C ⥤ _root_.DerivedCategory D)
    (β : W ⋙ (IsoAlgebra.forget Q).mapDerivedCategory ≅
      (IsoAlgebra.forget P).mapDerivedCategory ⋙ F)
    (ε : F ⋙ Q.mapDerivedCategory ≅ P.mapDerivedCategory ⋙ F)
    (b : L.mapHomotopyCategory (.up ℤ) ⋙ _root_.DerivedCategory.Qh ⟶
      _root_.DerivedCategory.Qh ⋙ F)
    (J : HomotopyCategory (IsoAlgebra P) (.up ℤ))
    (a : _root_.DerivedCategory.Qh.obj
        (((IsoAlgebra.mapOfNatIso e).mapHomotopyCategory (.up ℤ)).obj J) ⟶
      W.obj (_root_.DerivedCategory.Qh.obj J)) [IsIso a]
    (hβ : (IsoAlgebra.forget Q).mapDerivedCategory.map a ≫
        β.hom.app (_root_.DerivedCategory.Qh.obj J) ≫
        F.map ((IsoAlgebra.forget P).mapDerivedCategoryFactorsh.hom.app J) =
      (IsoAlgebra.forget Q).mapDerivedCategoryFactorsh.hom.app
          (((IsoAlgebra.mapOfNatIso e).mapHomotopyCategory (.up ℤ)).obj J) ≫
        b.app (((IsoAlgebra.forget P).mapHomotopyCategory (.up ℤ)).obj J))
    (hε : ∀ T : HomotopyCategory C (.up ℤ),
      Q.mapDerivedCategory.map (b.app T) ≫
          ε.hom.app (_root_.DerivedCategory.Qh.obj T) ≫
          F.map (P.mapDerivedCategoryFactorsh.hom.app T) =
        Q.mapDerivedCategoryFactorsh.hom.app ((L.mapHomotopyCategory (.up ℤ)).obj T) ≫
          _root_.DerivedCategory.Qh.map
            ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app T) ≫
          b.app ((P.mapHomotopyCategory (.up ℤ)).obj T)) :
    Q.mapDerivedCategory.map (β.hom.app (_root_.DerivedCategory.Qh.obj J)) ≫
        ε.hom.app ((IsoAlgebra.forget P).mapDerivedCategory.obj
          (_root_.DerivedCategory.Qh.obj J)) ≫
        F.map ((localizedStructure P).hom.app (_root_.DerivedCategory.Qh.obj J)) =
      (localizedStructure Q).hom.app (W.obj (_root_.DerivedCategory.Qh.obj J)) ≫
        β.hom.app (_root_.DerivedCategory.Qh.obj J) := by
  let r := IsoAlgebra.forget P
  let s := IsoAlgebra.forget Q
  let M := IsoAlgebra.mapOfNatIso e
  let T := (r.mapHomotopyCategory (.up ℤ)).obj J
  let H := (M.mapHomotopyCategory (.up ℤ)).obj J
  have hθ : _root_.DerivedCategory.Qh.map
      ((NatTrans.mapHomotopyCategory (IsoAlgebra.strNatIso Q).hom (.up ℤ)).app H) =
      _root_.DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app T) ≫
        _root_.DerivedCategory.Qh.map ((L.mapHomotopyCategory (.up ℤ)).map
          ((NatTrans.mapHomotopyCategory (IsoAlgebra.strNatIso P).hom (.up ℤ)).app J)) := by
    rw [← _root_.DerivedCategory.Qh.map_comp]
    congr 1
  rw [← cancel_epi (Q.mapDerivedCategory.map (s.mapDerivedCategory.map a))]
  rw [← cancel_mono (F.map (r.mapDerivedCategoryFactorsh.hom.app J))]
  simp only [Category.assoc]
  rw [← F.map_comp, structure_fac]
  simp only [Functor.map_comp]
  erw [← ε.hom.naturality_assoc]
  simp only [Functor.comp_map]
  erw [← Q.mapDerivedCategory.map_comp_assoc, ← Q.mapDerivedCategory.map_comp_assoc,
    Category.assoc, hβ]
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% (hε T)]
  erw [← b.naturality]
  simp only [Functor.comp_map]
  erw [← reassoc_of% hθ]
  erw [(localizedStructure Q).hom.naturality_assoc a]
  erw [hβ, reassoc_of% (structure_fac Q H)]
  rfl

private theorem natTrans_ext_kinjective
    [Abelian.HasKInjectiveResolutions C]
    {E : Type*} [Category* E] {F G : _root_.DerivedCategory C ⥤ E}
    {α β : F ⟶ G}
    (h : ∀ (J : CochainComplex C ℤ) [J.IsKInjective],
      α.app (_root_.DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient _ (.up ℤ)).obj J)) =
      β.app (_root_.DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient _ (.up ℤ)).obj J))) : α = β := by
  ext K
  obtain ⟨J, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage
    (F := HomotopyCategory.KInjectives.Qh (C := C)) K
  obtain ⟨J, _, rfl⟩ := HomotopyCategory.KInjectives.mk_surjective J
  rw [← cancel_epi (F.map e.hom), α.naturality, β.naturality]
  erw [h J]
  rfl

private theorem structure_compatibility_of_kinjective
    (P : C ⥤ C) (Q : D ⥤ D) [P.Additive] [Q.Additive]
    [P.IsEquivalence] [Q.IsEquivalence]
    [HasDerivedCategory.{w} (IsoAlgebra P)] [HasDerivedCategory.{w} (IsoAlgebra Q)]
    [Abelian.HasKInjectiveResolutions (IsoAlgebra P)]
    (W : _root_.DerivedCategory (IsoAlgebra P) ⥤ _root_.DerivedCategory (IsoAlgebra Q))
    (F : _root_.DerivedCategory C ⥤ _root_.DerivedCategory D)
    (β : W ⋙ (IsoAlgebra.forget Q).mapDerivedCategory ≅
      (IsoAlgebra.forget P).mapDerivedCategory ⋙ F)
    (ε : F ⋙ Q.mapDerivedCategory ≅ P.mapDerivedCategory ⋙ F)
    (h : ∀ (J : CochainComplex (IsoAlgebra P) ℤ) [J.IsKInjective],
      Q.mapDerivedCategory.map (β.hom.app (_root_.DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient _ (.up ℤ)).obj J))) ≫
          ε.hom.app ((IsoAlgebra.forget P).mapDerivedCategory.obj
            (_root_.DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj J))) ≫
          F.map ((localizedStructure P).hom.app (_root_.DerivedCategory.Qh.obj
            ((HomotopyCategory.quotient _ (.up ℤ)).obj J))) =
        (localizedStructure Q).hom.app (W.obj (_root_.DerivedCategory.Qh.obj
            ((HomotopyCategory.quotient _ (.up ℤ)).obj J))) ≫
          β.hom.app (_root_.DerivedCategory.Qh.obj
            ((HomotopyCategory.quotient _ (.up ℤ)).obj J)))
    (K : _root_.DerivedCategory (IsoAlgebra P)) :
    Q.mapDerivedCategory.map (β.hom.app K) ≫
        ε.hom.app ((IsoAlgebra.forget P).mapDerivedCategory.obj K) ≫
        F.map ((localizedStructure P).hom.app K) =
      (localizedStructure Q).hom.app (W.obj K) ≫ β.hom.app K := by
  let r := (IsoAlgebra.forget P).mapDerivedCategory
  let s := (IsoAlgebra.forget Q).mapDerivedCategory
  let α : (W ⋙ s) ⋙ Q.mapDerivedCategory ⟶ r ⋙ F :=
    Functor.whiskerRight β.hom Q.mapDerivedCategory ≫
      Functor.whiskerLeft r ε.hom ≫ Functor.whiskerRight (localizedStructure P).hom F
  let γ : (W ⋙ s) ⋙ Q.mapDerivedCategory ⟶ r ⋙ F :=
    Functor.whiskerLeft W (localizedStructure Q).hom ≫ β.hom
  have hh : α = γ := natTrans_ext_kinjective (fun J _ ↦ by
    simpa only [α, γ, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.comp_obj, Category.id_comp, Category.comp_id, Category.assoc] using h J)
  simpa only [α, γ, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.comp_obj, Category.id_comp, Category.comp_id, Category.assoc] using congr_app hh K

private theorem exact_structure
    (P : C ⥤ C) (Q : D ⥤ D) [P.Additive] [Q.Additive]
    [P.IsEquivalence] [Q.IsEquivalence] (L : C ⥤ D) [L.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [HasDerivedCategory.{w} (IsoAlgebra P)] [HasDerivedCategory.{w} (IsoAlgebra Q)]
    [Abelian.HasKInjectiveResolutions (IsoAlgebra P)]
    (e : L ⋙ Q ≅ P ⋙ L) (K : _root_.DerivedCategory (IsoAlgebra P)) :
    Q.mapDerivedCategory.map ((exactForgetComparison P Q L e).hom.app K) ≫
        (Functor.mapDerivedCategorySquareIso e).hom.app
          ((IsoAlgebra.forget P).mapDerivedCategory.obj K) ≫
        L.mapDerivedCategory.map ((localizedStructure P).hom.app K) =
      (localizedStructure Q).hom.app ((IsoAlgebra.mapOfNatIso e).mapDerivedCategory.obj K) ≫
        (exactForgetComparison P Q L e).hom.app K := by
  apply structure_compatibility_of_kinjective P Q _ _ _ _ _ K
  intro J _
  let M := IsoAlgebra.mapOfNatIso e
  let r := IsoAlgebra.forget P
  let s := IsoAlgebra.forget Q
  let T := (HomotopyCategory.quotient _ (.up ℤ)).obj J
  apply model_structure P Q L e M.mapDerivedCategory L.mapDerivedCategory
    (exactForgetComparison P Q L e) (Functor.mapDerivedCategorySquareIso e)
    L.mapDerivedCategoryFactorsh.inv T (M.mapDerivedCategoryFactorsh.inv.app T)
  · change s.mapDerivedCategory.map (M.mapDerivedCategoryFactorsh.inv.app T) ≫
        (Functor.mapDerivedCategorySquareIso (IsoAlgebra.mapOfNatIsoCompForgetIso e)).hom.app
          (_root_.DerivedCategory.Qh.obj T) ≫
        L.mapDerivedCategory.map (r.mapDerivedCategoryFactorsh.hom.app T) = _
    rw [← cancel_mono (L.mapDerivedCategoryFactorsh.hom.app
      ((r.mapHomotopyCategory (.up ℤ)).obj T))]
    simp only [Category.assoc]
    rw [exactSquare_fac]
    rw [← s.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
    have he : _root_.DerivedCategory.Qh.map
        ((NatTrans.mapHomotopyCategory
          (IsoAlgebra.mapOfNatIsoCompForgetIso e).hom (.up ℤ)).app T) = 𝟙 _ := by
      change _root_.DerivedCategory.Qh.map
        ((HomotopyCategory.quotient _ (.up ℤ)).map (𝟙 _)) = _
      simp only [CategoryTheory.Functor.map_id]
      rfl
    erw [he, Category.comp_id, Iso.inv_hom_id_app, Category.comp_id]
  · intro A
    rw [← cancel_mono (L.mapDerivedCategoryFactorsh.hom.app
      ((P.mapHomotopyCategory (.up ℤ)).obj A))]
    simp only [Category.assoc, Iso.inv_hom_id_app]
    rw [exactSquare_fac]
    rw [← Q.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

end Compatibility

section Composition

private theorem structure_composition
    {A₀ A₁ A₂ B₀ B₁ B₂ : Type*}
    [Category* A₀] [Category* A₁] [Category* A₂]
    [Category* B₀] [Category* B₁] [Category* B₂]
    (U₀ : A₀ ⥤ B₀) (U₁ : A₁ ⥤ B₁) (U₂ : A₂ ⥤ B₂)
    (W₀ : A₀ ⥤ A₁) (W₁ : A₁ ⥤ A₂)
    (F₀ : B₀ ⥤ B₁) (F₁ : B₁ ⥤ B₂)
    (P₀ : B₀ ⥤ B₀) (P₁ : B₁ ⥤ B₁) (P₂ : B₂ ⥤ B₂)
    (τ₀ : U₀ ⋙ P₀ ≅ U₀) (τ₁ : U₁ ⋙ P₁ ≅ U₁) (τ₂ : U₂ ⋙ P₂ ≅ U₂)
    (β₀ : W₀ ⋙ U₁ ≅ U₀ ⋙ F₀) (β₁ : W₁ ⋙ U₂ ≅ U₁ ⋙ F₁)
    (ε₀ : F₀ ⋙ P₁ ≅ P₀ ⋙ F₀) (ε₁ : F₁ ⋙ P₂ ≅ P₁ ⋙ F₁)
    (h₀ : ∀ K, P₁.map (β₀.hom.app K) ≫ ε₀.hom.app (U₀.obj K) ≫
      F₀.map (τ₀.hom.app K) = τ₁.hom.app (W₀.obj K) ≫ β₀.hom.app K)
    (h₁ : ∀ K, P₂.map (β₁.hom.app K) ≫ ε₁.hom.app (U₁.obj K) ≫
      F₁.map (τ₁.hom.app K) = τ₂.hom.app (W₁.obj K) ≫ β₁.hom.app K)
    (K : A₀) :
    let β := Functor.associator W₀ W₁ U₂ ≪≫
      Functor.isoWhiskerLeft W₀ β₁ ≪≫ (Functor.associator W₀ U₁ F₁).symm ≪≫
        Functor.isoWhiskerRight β₀ F₁ ≪≫ Functor.associator U₀ F₀ F₁
    let ε := Functor.associator F₀ F₁ P₂ ≪≫
      Functor.isoWhiskerLeft F₀ ε₁ ≪≫ (Functor.associator F₀ P₁ F₁).symm ≪≫
        Functor.isoWhiskerRight ε₀ F₁ ≪≫ Functor.associator P₀ F₀ F₁
    P₂.map (β.hom.app K) ≫ ε.hom.app (U₀.obj K) ≫ (F₀ ⋙ F₁).map (τ₀.hom.app K) =
      τ₂.hom.app ((W₀ ⋙ W₁).obj K) ≫ β.hom.app K := by
  dsimp only
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.comp_obj, Functor.comp_map, Category.id_comp, Category.comp_id]
  rw [Functor.map_comp]
  simp only [Category.assoc]
  have hn := ε₁.hom.naturality (β₀.hom.app K)
  change P₂.map (F₁.map (β₀.hom.app K)) ≫ ε₁.hom.app (F₀.obj (U₀.obj K)) =
    ε₁.hom.app (U₁.obj (W₀.obj K)) ≫ F₁.map (P₁.map (β₀.hom.app K)) at hn
  rw [reassoc_of% hn]
  rw [← F₁.map_comp, ← F₁.map_comp, h₀ K, F₁.map_comp]
  rw [reassoc_of% (h₁ (W₀.obj K))]

end Composition

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]

omit [Fact (ringChar k₀ ≠ l)] in
private theorem proper_structure
    {X Y : Scheme.{u}} [X.Over (Spec (.of k₀))] [Y.Over (Spec (.of k₀))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k₀))] (c : Compactification f)
    (K : _root_.DerivedCategory (ProEtaleWeilSheaf k₀ l c.Z)) :
    (frobenius k₀ l Y).map ((properComparison k₀ l f c).hom.app K) ≫
        (rightExchange _ _ _
          (ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso
            l c.g (comp_over c.g (Spec (.of k₀))))).hom.app ((forget k₀ l c.Z).obj K) ≫
        (ProEtale.adicLowerStar l
          (Scheme.Hom.geometricFiberMap c.g
            (comp_over c.g (Spec (.of k₀))))).rightDerivedFunctor.map
          ((structureIso k₀ l c.Z).hom.app K) =
      (structureIso k₀ l Y).hom.app
          ((ProEtaleWeilSheaf.lowerStar k₀ l c.g).rightDerivedFunctor.obj K) ≫
        (properComparison k₀ l f c).hom.app K := by
  let P := WeilSheaf.frobeniusPullback k₀ l c.Z
  let Q := WeilSheaf.frobeniusPullback k₀ l Y
  let L := ProEtale.adicLowerStar l
    (Scheme.Hom.geometricFiberMap c.g (comp_over c.g (Spec (.of k₀))))
  let e := ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso
    l c.g (comp_over c.g (Spec (.of k₀)))
  apply structure_compatibility_of_kinjective P Q
    (ProEtaleWeilSheaf.lowerStar k₀ l c.g).rightDerivedFunctor L.rightDerivedFunctor
    (properComparison k₀ l f c) (rightExchange P Q L e) _ K
  intro J _
  apply model_structure P Q L e
    (ProEtaleWeilSheaf.lowerStar k₀ l c.g).rightDerivedFunctor L.rightDerivedFunctor
    (properComparison k₀ l f c) (rightExchange P Q L e) L.rightDerivedFunctorUnit
    ((HomotopyCategory.quotient _ (.up ℤ)).obj J)
    ((ProEtaleWeilSheaf.lowerStar k₀ l c.g).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj J))
  · exact nativeWeil_proper_normalization k₀ l f c J inferInstance
  · exact rightExchange_unit P Q L e

-- Preserve the original characteristic binder; the categorical proof is uniform in it.
set_option linter.unusedSectionVars false in
/-- The specified comparison intertwines the localized Weil structure with the native
Frobenius exchange.
Source: blueprint `lem-fix-weil-operations`, paragraphs 1--2; native comparison proof,
step 6. (blueprint: lem-sf-native-weil-comparison-structure)

Proof: the defining derived-unit equations give the normalization of the proper
Frobenius exchange. On a K-injective Weil complex, precompose with Frobenius applied
to the forgotten derived unit and postcompose with the image of the forgetful
localization factor. These are isomorphisms. The proper normalization and naturality
of the ordinary derived unit reduce the desired equality to the termwise definition
of the transported Weil structure: exchange followed by the image of the source
structure. Every derived Weil object is isomorphic to such a K-injective model, so
naturality extends the equality to every object. The same calculation for the exact
open functor uses its inverse localization factors as units. Finally, expand beta
and the compact-support exchange into open/proper factors. Naturality of the proper
exchange moves the open comparison past it, and the two structure equations combine
to give the displayed identity. -/
theorem nativeWeil_comparison_structure
    {X Y : Scheme.{u}} [X.Over (Spec (.of k₀))] [Y.Over (Spec (.of k₀))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k₀))] (c : Compactification f)
    (K : _root_.DerivedCategory (ProEtaleWeilSheaf k₀ l X)) :
    (frobenius k₀ l Y).map ((comparison k₀ l f c).hom.app K) ≫
        (exchange k₀ l f c).hom.app ((forget k₀ l X).obj K) ≫
        (ordinaryImage k₀ l f c).map ((structureIso k₀ l X).hom.app K) =
      (structureIso k₀ l Y).hom.app
          ((ProEtaleWeilSheaf.rightDerivedLowerShriek k₀ l f c).obj K) ≫
        (comparison k₀ l f c).hom.app K  := by
  let P := WeilSheaf.frobeniusPullback k₀ l c.Z
  let L := ProEtale.adicLowerStar l
    (Scheme.Hom.geometricFiberMap c.g (comp_over c.g (Spec (.of k₀))))
  let O := ProEtale.adicOpenImmersionLowerShriek l
    (Scheme.Hom.geometricFiberMap c.i (comp_over c.i (Spec (.of k₀))))
  let e := ProEtale.adicOpenImmersionLowerShriekGeometricFiberMapCompFrobeniusIso
    l c.i (comp_over c.i (Spec (.of k₀)))
  let E := rightExchange P (WeilSheaf.frobeniusPullback k₀ l Y) L
    (ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso
      l c.g (comp_over c.g (Spec (.of k₀))))
  exact structure_composition
    (forget k₀ l X) (forget k₀ l c.Z) (forget k₀ l Y)
    (ProEtaleWeilSheaf.extensionByZero k₀ l c.i).mapDerivedCategory
    (ProEtaleWeilSheaf.lowerStar k₀ l c.g).rightDerivedFunctor
    O.mapDerivedCategory L.rightDerivedFunctor
    (frobenius k₀ l X) (frobenius k₀ l c.Z) (frobenius k₀ l Y)
    (structureIso k₀ l X) (structureIso k₀ l c.Z) (structureIso k₀ l Y)
    (openComparison k₀ l f c) (properComparison k₀ l f c)
    (Functor.mapDerivedCategorySquareIso e) E
    (fun A ↦ exact_structure (WeilSheaf.frobeniusPullback k₀ l X) P O e A)
    (proper_structure k₀ l f c) K

end AlgebraicGeometry.NativeWeilInduction
