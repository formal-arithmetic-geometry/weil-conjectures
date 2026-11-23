/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift

import WeilConjectures.CategoryTheory.DerivedCategory.ProEtaleCoefficients.DerivedMonoidalClosed

/-!
# Closed derived tensor structure and integer-shift comparisons

The statement packages the derived closed structure, the canonical two-variable shift
comparisons, and their normalization by the lax-monoidal comparison of the localization.
The chain comparisons are Mathlib's `mapBifunctorShift₁Iso` and `mapBifunctorShift₂Iso`:
the first is identity on each total-tensor summand and the second multiplies the summand
of bidegree `(p,q)` by `(-1)^(p*b)`.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe w v u

namespace CategoryTheory.NatTrans.CommShift

-- Check shift compatibility on resolving objects, then cancel the localized resolution.
private lemma of_left_resolutions
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {A : Type*} [AddMonoid A] [HasShift C A] [HasShift D A] [HasShift E A]
    {F₁ F₂ : C ⥤ D} (τ : F₁ ⟶ F₂) [F₁.CommShift A] [F₂.CommShift A]
    (L : E ⥤ C) [L.CommShift A]
    [NatTrans.CommShift (Functor.whiskerLeft L τ) A]
    (h : ∀ X, ∃ (Y : E) (f : L.obj Y ⟶ X), IsIso (F₁.map f)) :
    NatTrans.CommShift τ A where
  shift_comm a := by
    ext X
    obtain ⟨Y, f, hf⟩ := h X
    have hY : (F₁.commShiftIso a).hom.app (L.obj Y) ≫ (τ.app (L.obj Y))⟦a⟧' =
        τ.app ((L.obj Y)⟦a⟧) ≫ (F₂.commShiftIso a).hom.app (L.obj Y) := by
      have h := NatTrans.shift_app_comm (Functor.whiskerLeft L τ) a Y
      simp only [Functor.comp_obj, Functor.whiskerLeft_app, Functor.commShiftIso_comp_hom_app,
        Category.assoc] at h
      rw [← τ.naturality_assoc] at h
      exact (cancel_epi _).1 h
    have eq : F₁.map (f⟦a⟧') = (F₁.commShiftIso a).hom.app (L.obj Y) ≫
        (F₁.map f)⟦a⟧' ≫ (F₁.commShiftIso a).inv.app X := by
      rw [← Functor.commShiftIso_hom_naturality_assoc, Iso.hom_inv_id_app]
      simp only [Functor.comp_obj, Category.comp_id]
    have : IsIso (F₁.map (f⟦a⟧')) := by rw [eq]; infer_instance
    dsimp
    rw [← cancel_epi (F₁.map (f⟦a⟧')), Functor.commShiftIso_hom_naturality_assoc,
      ← Functor.map_comp, τ.naturality, Functor.map_comp, reassoc_of% hY,
      τ.naturality_assoc, Functor.commShiftIso_hom_naturality]
end CategoryTheory.NatTrans.CommShift

namespace DerivedCategory

section NativeTensorCoherence

open TensorCommShift₂

variable (C : Type u) [Category.{v} C] [Abelian C]
  [IsGrothendieckAbelian.{v} C] [HasDerivedCategory.{w} C]
  [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]
  [DerivedCategory.Qh.HasDerivedMonoidalCategory (HomotopyCategory.quasiIso C (.up ℤ))]

-- The K-flat lifting gives compatibility; naturality extends it to every first factor.
private theorem nativeTensoratorL_commShift_right (X : CochainComplex C ℤ) :
    NatTrans.CommShift
      (F₁ := L C ⋙ (curriedTensor (DerivedCategory C)).obj ((L C).obj X))
      (F₂ := (curriedTensor (CochainComplex C ℤ)).obj X ⋙ L C)
      ((Functor.LaxMonoidal.μNatTrans (L C)).app X) ℤ := by
  let R : (HomologicalComplex.quasiIso C (.up ℤ)).localizerMorphismKFlat.LeftResolution X :=
    Classical.arbitrary _
  have : IsIso ((L C).map R.w) := Localization.inverts (L C) _ _ R.hw
  let τP : L C ⋙ (curriedTensor (DerivedCategory C)).obj ((L C).obj R.X₁.obj) ⟶
      (curriedTensor (CochainComplex C ℤ)).obj R.X₁.obj ⋙ L C :=
    (Functor.LaxMonoidal.μNatTrans (L C)).app R.X₁.obj
  have hc : NatTrans.CommShift τP ℤ := by
    have hc := Functor.CommShift₂OfLocalization.commShift_liftingIsoApp (M := ℤ)
      (LKFlat C) (L C) (HomologicalComplex.quasiIso C (.up ℤ)).WKFlat
      (HomologicalComplex.quasiIso C (.up ℤ)) (F C) (curriedTensor (DerivedCategory C)) R.X₁
    have heq : τP = Functor.CommShift₂OfLocalization.liftingIsoApp
        (LKFlat C) (L C) (HomologicalComplex.quasiIso C (.up ℤ)).WKFlat
        (HomologicalComplex.quasiIso C (.up ℤ)) (F C)
        (curriedTensor (DerivedCategory C)) R.X₁ := by
      ext Z
      change (Functor.LaxMonoidal.μ Qh _ _ ≫ Qh.map (𝟙 _)) =
        Functor.LaxMonoidal.μ Qh _ _
      simp
    rw [heq]
    exact hc
  let α := Functor.whiskerLeft (L C)
    ((curriedTensor (DerivedCategory C)).map ((L C).map R.w))
  let β := Functor.whiskerRight ((curriedTensor (CochainComplex C ℤ)).map R.w) (L C)
  have hβ : NatTrans.CommShift β ℤ := by
    dsimp [β]
    have := Functor.CommShift₂.commShift_map
      (G := curriedTensor (CochainComplex C ℤ)) (h := .int) R.w
    infer_instance
  have : NatTrans.CommShift (inv α) ℤ := NatTrans.CommShift.of_isIso α ℤ
  have hfac : (Functor.LaxMonoidal.μNatTrans (L C)).app X =
      inv α ≫ τP ≫ β := by
    rw [IsIso.eq_inv_comp]
    exact (Functor.LaxMonoidal.μNatTrans (L C)).naturality R.w
  rw [hfac]
  infer_instance

-- Restrict the flipped tensorator to K-flat complexes and descend along resolutions.
private theorem nativeTensoratorL_commShift_left (Z : CochainComplex C ℤ) :
    NatTrans.CommShift
      (F₁ := L C ⋙ (curriedTensor (DerivedCategory C)).flip.obj ((L C).obj Z))
      (F₂ := (curriedTensor (CochainComplex C ℤ)).flip.obj Z ⋙ L C)
      ((Functor.LaxMonoidal.μNatTrans (L C)).flipApp Z) ℤ := by
  let τ : L C ⋙ (curriedTensor (DerivedCategory C)).flip.obj ((L C).obj Z) ⟶
      (curriedTensor (CochainComplex C ℤ)).flip.obj Z ⋙ L C :=
    (Functor.LaxMonoidal.μNatTrans (L C)).flipApp Z
  have hc := Functor.CommShift₂OfLocalization.commShift_liftingIsoApp (M := ℤ)
    (L C) (LKFlat C) (HomologicalComplex.quasiIso C (.up ℤ))
    (HomologicalComplex.quasiIso C (.up ℤ)).WKFlat (F C).flip
    (curriedTensor (DerivedCategory C)).flip Z
  have heq : Functor.whiskerLeft (CochainComplex.ιKFlat C) τ =
      (Functor.associator (CochainComplex.ιKFlat C) (L C)
        ((curriedTensor (DerivedCategory C)).flip.obj ((L C).obj Z))).inv ≫
        Functor.CommShift₂OfLocalization.liftingIsoApp
          (L C) (LKFlat C) (HomologicalComplex.quasiIso C (.up ℤ))
          (HomologicalComplex.quasiIso C (.up ℤ)).WKFlat (F C).flip
          (curriedTensor (DerivedCategory C)).flip Z ≫
        (Functor.associator (CochainComplex.ιKFlat C)
          ((curriedTensor (CochainComplex C ℤ)).flip.obj Z) (L C)).hom := by
    ext P
    change (Functor.LaxMonoidal.μ Qh _ _ ≫ Qh.map (𝟙 _)) =
      𝟙 _ ≫ Functor.LaxMonoidal.μ Qh _ _ ≫ 𝟙 _
    simp
  have : NatTrans.CommShift (Functor.whiskerLeft (CochainComplex.ιKFlat C) τ) ℤ := by
    rw [heq]
    infer_instance
  apply CategoryTheory.NatTrans.CommShift.of_left_resolutions τ (CochainComplex.ιKFlat C)
  intro X
  let R : (HomologicalComplex.quasiIso C (.up ℤ)).localizerMorphismKFlat.LeftResolution X :=
    Classical.arbitrary _
  have : IsIso ((L C).map R.w) := Localization.inverts (L C) _ _ R.hw
  refine ⟨R.X₁, R.w, ?_⟩
  change IsIso (((curriedTensor (DerivedCategory C)).flip.obj ((L C).obj Z)).map
    ((L C).map R.w))
  infer_instance

-- Transport the tensorator through the shift-compatible comparison L ≅ Q.
private theorem nativeTensoratorQ_commShift_right (X : CochainComplex C ℤ)
    (h : NatTrans.CommShift
      (F₁ := L C ⋙ (curriedTensor (DerivedCategory C)).obj ((L C).obj X))
      (F₂ := (curriedTensor (CochainComplex C ℤ)).obj X ⋙ L C)
      ((Functor.LaxMonoidal.μNatTrans (L C)).app X) ℤ) :
    NatTrans.CommShift
      (F₁ := Q (C := C) ⋙ (curriedTensor (DerivedCategory C)).obj (Q.obj X))
      (F₂ := (curriedTensor (CochainComplex C ℤ)).obj X ⋙ Q)
      ((Functor.LaxMonoidal.μNatTrans (Q (C := C))).app X) ℤ := by
  let τL : L C ⋙ (curriedTensor (DerivedCategory C)).obj ((L C).obj X) ⟶
      (curriedTensor (CochainComplex C ℤ)).obj X ⋙ L C :=
    (Functor.LaxMonoidal.μNatTrans (L C)).app X
  have hτL : NatTrans.CommShift τL ℤ := h
  let e := quotientCompQhIso C
  let α₁ := Functor.whiskerRight e.inv
    ((curriedTensor (DerivedCategory C)).obj (Q.obj X))
  let α₂ := Functor.whiskerLeft (L C)
    ((curriedTensor (DerivedCategory C)).map (e.inv.app X))
  let β := Functor.whiskerLeft ((curriedTensor (CochainComplex C ℤ)).obj X) e.hom
  have hfac : (Functor.LaxMonoidal.μNatTrans (Q (C := C))).app X =
      α₁ ≫ α₂ ≫ τL ≫ β := by
    ext Z
    change (e.inv.app X ⊗ₘ e.inv.app Z) ≫ _ ≫ _ =
      (Q.obj X ◁ e.inv.app Z) ≫ (e.inv.app X ▷ (L C).obj Z) ≫ _ ≫ _
    simp only [tensorHom_def', Category.assoc]
    rfl
  rw [hfac]
  infer_instance

private theorem nativeTensoratorQ_commShift_left (X : CochainComplex C ℤ)
    (h : NatTrans.CommShift
      (F₁ := L C ⋙ (curriedTensor (DerivedCategory C)).flip.obj ((L C).obj X))
      (F₂ := (curriedTensor (CochainComplex C ℤ)).flip.obj X ⋙ L C)
      ((Functor.LaxMonoidal.μNatTrans (L C)).flipApp X) ℤ) :
    NatTrans.CommShift
      (F₁ := Q (C := C) ⋙ (curriedTensor (DerivedCategory C)).flip.obj (Q.obj X))
      (F₂ := (curriedTensor (CochainComplex C ℤ)).flip.obj X ⋙ Q)
      ((Functor.LaxMonoidal.μNatTrans (Q (C := C))).flipApp X) ℤ := by
  let τL : L C ⋙ (curriedTensor (DerivedCategory C)).flip.obj ((L C).obj X) ⟶
      (curriedTensor (CochainComplex C ℤ)).flip.obj X ⋙ L C :=
    (Functor.LaxMonoidal.μNatTrans (L C)).flipApp X
  have hτL : NatTrans.CommShift τL ℤ := h
  let e := quotientCompQhIso C
  let α₁ := Functor.whiskerRight e.inv
    ((curriedTensor (DerivedCategory C)).flip.obj (Q.obj X))
  let α₂ := Functor.whiskerLeft (L C)
    ((curriedTensor (DerivedCategory C)).flip.map (e.inv.app X))
  let β := Functor.whiskerLeft ((curriedTensor (CochainComplex C ℤ)).flip.obj X) e.hom
  have hfac : (Functor.LaxMonoidal.μNatTrans (Q (C := C))).flipApp X =
      α₁ ≫ α₂ ≫ τL ≫ β := by
    ext Z
    change (e.inv.app Z ⊗ₘ e.inv.app X) ≫ _ ≫ _ =
      (e.inv.app Z ▷ Q.obj X) ≫ ((L C).obj Z ◁ e.inv.app X) ≫ _ ≫ _
    simp only [tensorHom_def, Category.assoc]
    rfl
  rw [hfac]
  infer_instance

private theorem nativeDerivedClosedTensorShift_left_normalization :
    ∀ (X : CochainComplex C ℤ) (Z : CochainComplex C ℤ) (a : ℤ),
      Functor.LaxMonoidal.μ (DerivedCategory.Q (C := C)) (X⟦a⟧) Z ≫
          (DerivedCategory.Q (C := C)).map
            (CochainComplex.mapBifunctorShift₁Iso X Z (curriedTensor C) a).hom ≫
          ((DerivedCategory.Q (C := C)).commShiftIso a).hom.app
            (CochainComplex.mapBifunctor X Z (curriedTensor C)) =
        ((Functor.uncurry.obj (curriedTensor (DerivedCategory C))).map
          (CategoryTheory.Prod.mkHom
            (((DerivedCategory.Q (C := C)).commShiftIso a).hom.app X)
            (𝟙 _))) ≫
          (((curriedTensor (DerivedCategory C)).flip.obj
            ((DerivedCategory.Q (C := C)).obj Z)).commShiftIso a).hom.app
            ((DerivedCategory.Q (C := C)).obj X) ≫
          (shiftFunctor (DerivedCategory C) a).map
            (Functor.LaxMonoidal.μ (DerivedCategory.Q (C := C)) X Z) := by
  intro X Z a
  have hL := nativeTensoratorL_commShift_left C Z
  have hc := nativeTensoratorQ_commShift_left C Z hL
  have he := (NatTrans.shift_app_comm
    (F₁ := Q (C := C) ⋙ (curriedTensor (DerivedCategory C)).flip.obj (Q.obj Z))
    (F₂ := (curriedTensor (CochainComplex C ℤ)).flip.obj Z ⋙ Q)
    ((Functor.LaxMonoidal.μNatTrans (Q (C := C))).flipApp Z) a X).symm
  have ht : (((curriedTensor (CochainComplex C ℤ)).flip.obj Z).commShiftIso a).hom.app X =
      (CochainComplex.mapBifunctorShift₁Iso X Z (curriedTensor C) a).hom := by
    exact Functor.commShiftIso_map₂CochainComplex_flip_hom_app (curriedTensor C) X Z a
  simp only [Functor.commShiftIso_comp_hom_app, Category.assoc] at he
  rw [ht] at he
  simp only [NatTrans.flipApp, flipFunctor_map_app_app,
    Functor.LaxMonoidal.μNatTrans_app_app] at he
  simp only [Functor.uncurry_obj_map, Functor.comp_obj, curriedTensor_obj_map,
    curriedTensor_map_app, Functor.flip_obj_map, Functor.flip_obj_obj, curriedTensor_obj_obj,
    MonoidalCategory.whiskerLeft_id, Category.comp_id] at he ⊢
  convert he using 1

private theorem nativeDerivedClosedTensorShift_right_normalization :
    ∀ (X : CochainComplex C ℤ) (Z : CochainComplex C ℤ) (b : ℤ),
      Functor.LaxMonoidal.μ (DerivedCategory.Q (C := C)) X (Z⟦b⟧) ≫
          (DerivedCategory.Q (C := C)).map
            (CochainComplex.mapBifunctorShift₂Iso X Z (curriedTensor C) b).hom ≫
          ((DerivedCategory.Q (C := C)).commShiftIso b).hom.app
            (CochainComplex.mapBifunctor X Z (curriedTensor C)) =
        ((Functor.uncurry.obj (curriedTensor (DerivedCategory C))).map
          (CategoryTheory.Prod.mkHom
            (𝟙 ((DerivedCategory.Q (C := C)).obj X))
            (((DerivedCategory.Q (C := C)).commShiftIso b).hom.app Z))) ≫
          (((curriedTensor (DerivedCategory C)).obj
            ((DerivedCategory.Q (C := C)).obj X)).commShiftIso b).hom.app
            ((DerivedCategory.Q (C := C)).obj Z) ≫
          (shiftFunctor (DerivedCategory C) b).map
            (Functor.LaxMonoidal.μ (DerivedCategory.Q (C := C)) X Z) := by
  intro X Z a
  have hL := nativeTensoratorL_commShift_right C X
  have hc := nativeTensoratorQ_commShift_right C X hL
  have he := (NatTrans.shift_app_comm
    (F₁ := Q (C := C) ⋙ (curriedTensor (DerivedCategory C)).obj (Q.obj X))
    (F₂ := (curriedTensor (CochainComplex C ℤ)).obj X ⋙ Q)
    ((Functor.LaxMonoidal.μNatTrans (Q (C := C))).app X) a Z).symm
  have ht : (((curriedTensor (CochainComplex C ℤ)).obj X).commShiftIso a).hom.app Z =
      (CochainComplex.mapBifunctorShift₂Iso X Z (curriedTensor C) a).hom := by
    exact Functor.commShiftIso_map₂CochainComplex_hom_app (curriedTensor C) X Z a
  simp only [Functor.commShiftIso_comp_hom_app, Category.assoc] at he
  rw [ht] at he
  simp only [Functor.LaxMonoidal.μNatTrans_app_app] at he
  simp only [Functor.uncurry_obj_map, Functor.comp_obj, curriedTensor_obj_map,
    curriedTensor_map_app, curriedTensor_obj_obj,
    MonoidalCategory.id_whiskerRight, Category.id_comp] at he ⊢
  convert he using 1

end NativeTensorCoherence

/-- Closedness and the normalized integer-shift equations for the derived tensor.

The first conjunct is closedness, the second and third are the equations for the shifts of the
first and of the second variable of the tensorator, and the last two are the premises of the
final determination sentence. -/
theorem nativeDerivedClosedTensorShifts
    (C : Type u) [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{v} C] [HasDerivedCategory.{w} C]
    [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    [Qh.HasDerivedMonoidalCategory (HomotopyCategory.quasiIso C (.up ℤ))] :
    (∀ (K : DerivedCategory C),
      ∃ (R : DerivedCategory C ⥤ DerivedCategory C), Nonempty (tensorLeft K ⊣ R)) ∧
    (∀ (X : CochainComplex C ℤ) (Z : CochainComplex C ℤ) (a : ℤ),
        Functor.LaxMonoidal.μ (DerivedCategory.Q (C := C)) (X⟦a⟧) Z ≫
            (DerivedCategory.Q (C := C)).map
              (CochainComplex.mapBifunctorShift₁Iso X Z (curriedTensor C) a).hom ≫
            ((DerivedCategory.Q (C := C)).commShiftIso a).hom.app
              (CochainComplex.mapBifunctor X Z (curriedTensor C)) =
          ((Functor.uncurry.obj (curriedTensor (DerivedCategory C))).map
            (CategoryTheory.Prod.mkHom
              (((DerivedCategory.Q (C := C)).commShiftIso a).hom.app X)
              (𝟙 _))) ≫
            (((curriedTensor (DerivedCategory C)).flip.obj
              ((DerivedCategory.Q (C := C)).obj Z)).commShiftIso a).hom.app
              ((DerivedCategory.Q (C := C)).obj X) ≫
            (shiftFunctor (DerivedCategory C) a).map
              (Functor.LaxMonoidal.μ (DerivedCategory.Q (C := C)) X Z)) ∧
      (∀ (X : CochainComplex C ℤ) (Z : CochainComplex C ℤ) (b : ℤ),
        Functor.LaxMonoidal.μ (DerivedCategory.Q (C := C)) X (Z⟦b⟧) ≫
            (DerivedCategory.Q (C := C)).map
              (CochainComplex.mapBifunctorShift₂Iso X Z (curriedTensor C) b).hom ≫
            ((DerivedCategory.Q (C := C)).commShiftIso b).hom.app
              (CochainComplex.mapBifunctor X Z (curriedTensor C)) =
          ((Functor.uncurry.obj (curriedTensor (DerivedCategory C))).map
            (CategoryTheory.Prod.mkHom
              (𝟙 ((DerivedCategory.Q (C := C)).obj X))
              (((DerivedCategory.Q (C := C)).commShiftIso b).hom.app Z))) ≫
            (((curriedTensor (DerivedCategory C)).obj
              ((DerivedCategory.Q (C := C)).obj X)).commShiftIso b).hom.app
              ((DerivedCategory.Q (C := C)).obj Z) ≫
            (shiftFunctor (DerivedCategory C) b).map
              (Functor.LaxMonoidal.μ (DerivedCategory.Q (C := C)) X Z)) ∧
      (∀ (X : CochainComplex C ℤ) (_hX :
          (HomologicalComplex.quasiIso C (.up ℤ)).kFlat X) (Z : CochainComplex C ℤ),
        IsIso (Functor.LaxMonoidal.μ (DerivedCategory.Q (C := C)) X Z)) ∧
      (∀ (K : DerivedCategory C),
        ∃ (X : CochainComplex C ℤ),
          (HomologicalComplex.quasiIso C (.up ℤ)).kFlat X ∧
            Nonempty ((DerivedCategory.Q (C := C)).obj X ≅ K)) := by
  constructor
  · intro K
    exact (tensorLeft_isLeftAdjoint_of_hasFunctorialFlatResolution C K).exists_rightAdjoint
  constructor
  · exact nativeDerivedClosedTensorShift_left_normalization C
  constructor
  · exact nativeDerivedClosedTensorShift_right_normalization C
  constructor
  · intro X hX Z
    have : IsIso (Functor.LaxMonoidal.μ (Qh (C := C))
        ((HomotopyCategory.quotient C (.up ℤ)).obj X)
        ((HomotopyCategory.quotient C (.up ℤ)).obj Z)) :=
      DerivedMonoidal.isIso_counit_app_app_of_kFlat_left Qh _ _ _
        ((HomotopyCategory.kFlat_quotient_obj_iff _).2 hX)
    change IsIso (((quotientCompQhIso C).inv.app X ⊗ₘ
      (quotientCompQhIso C).inv.app Z) ≫
      (Functor.LaxMonoidal.μ (Qh (C := C)) _ _ ≫
        Qh.map (Functor.LaxMonoidal.μ (HomotopyCategory.quotient C (.up ℤ)) X Z)) ≫
      (quotientCompQhIso C).hom.app _)
    infer_instance
  · intro K
    obtain ⟨P, hP, ⟨e⟩⟩ := DerivedCategory.exists_kFlat_iso K
    obtain ⟨X, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
    refine ⟨X, (HomotopyCategory.kFlat_quotient_obj_iff _).1 hP, ?_⟩
    exact ⟨(DerivedCategory.quotientCompQhIso C).symm.app X ≪≫ e⟩

end DerivedCategory
