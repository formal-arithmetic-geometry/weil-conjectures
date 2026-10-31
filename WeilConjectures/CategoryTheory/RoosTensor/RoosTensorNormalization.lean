/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Roos.RoosComparisonHorizontalCoherenceSupplement
import WeilConjectures.CategoryTheory.Strict.StrictRoosAdditiveComparison
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
import WeilConjectures.CategoryTheory.ExactDerivedSquare.DerivedExactSquareCoherence
import all WeilConjectures.CategoryTheory.Strict.StrictRoosDerivedLimitComparisonSupplement

/-! # Tensor normalization of a unit-normalized Roos comparison

Source: Stacks Tag 0941, product-cone comparison and ordinary-limit inclusion.
(blueprint: lem-pur-roos-tensor-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.RoosTensor
universe u d

private theorem factorsh_quotient
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (P : CochainComplex A ℤ) :
    F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) =
      F.mapDerivedCategoryFactors.hom.app P := by
  rw [Functor.mapDerivedCategoryFactorsh_hom_app]
  simp only [DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv,
    Quotient.lift.isLift_hom]
  erw [CategoryTheory.Functor.map_id, DerivedCategory.Qh.map_id]
  erw [Category.comp_id, Category.comp_id, Category.id_comp]

section SquareHelpers

variable {A B Ap Bp : Type (u + 1)}
  [Category.{u} A] [Category.{u} B] [Category.{u} Ap] [Category.{u} Bp]
  [Abelian A] [Abelian B] [Abelian Ap] [Abelian Bp]
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory Ap] [HasDerivedCategory Bp]
  [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions Ap]
  (H : A ⥤ B) (G : Ap ⥤ Bp) (x : A ⥤ Ap) (y : B ⥤ Bp)
  [H.Additive] [G.Additive] [x.Additive] [y.Additive]
  [PreservesFiniteLimits x] [PreservesFiniteColimits x]
  [PreservesFiniteLimits y] [PreservesFiniteColimits y]
  [x.PreservesKInjectiveComplexes]

private theorem tensorSquare_normalized (c : H ⋙ y ≅ x ⋙ G) :
    ExactDerivedSquare.unitNormalized H G x y x.mapDerivedCategory y.mapDerivedCategory
      x.mapDerivedCategoryFactors y.mapDerivedCategoryFactors c.hom
      ((Functor.rightDerivedFunctorCompMapDerivedCategoryIso H y).symm ≪≫
        Functor.rightDerivedFunctorNatIso c ≪≫
        Functor.mapDerivedCategoryCompRightDerivedFunctorIso x G).hom := by
  intro I
  let P := (HomotopyCategory.quotient A (.up ℤ)).obj I
  have hstart : y.mapDerivedCategory.map (H.rightDerivedFunctorUnit.app P) =
      y.mapDerivedCategoryFactorsh.hom.app ((H.mapHomotopyCategory (.up ℤ)).obj P) ≫
        (Functor.rightDerivedFunctorCompMapDerivedCategoryUnit H y).app P := by
    have hi : (Functor.mapHomotopyCategoryCompIso
        (Iso.refl (H ⋙ y)) (.up ℤ)).inv.app P = 𝟙 _ := rfl
    simp only [Functor.rightDerivedFunctorCompMapDerivedCategoryUnit, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.associator_inv_app, hi, Category.id_comp, Category.comp_id]
    erw [DerivedCategory.Qh.map_id, Category.id_comp, Iso.hom_inv_id_app_assoc]
  have hnorm : y.mapDerivedCategory.map (H.rightDerivedFunctorUnit.app P) ≫
      ((Functor.rightDerivedFunctorCompMapDerivedCategoryIso H y).symm ≪≫
        Functor.rightDerivedFunctorNatIso c ≪≫
        Functor.mapDerivedCategoryCompRightDerivedFunctorIso x G).hom.app
          (DerivedCategory.Qh.obj P) ≫
      G.rightDerivedFunctor.map (x.mapDerivedCategoryFactorsh.hom.app P) =
    y.mapDerivedCategoryFactorsh.hom.app ((H.mapHomotopyCategory (.up ℤ)).obj P) ≫
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory c.hom (.up ℤ)).app P) ≫
      G.rightDerivedFunctorUnit.app ((x.mapHomotopyCategory (.up ℤ)).obj P) := by
    rw [hstart]
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc,
      Functor.rightDerivedFunctorCompMapDerivedCategoryIso,
      Functor.rightDerivedUnique, Functor.rightDerivedNatIso,
      Functor.rightDerivedFunctorNatIso, Functor.rightDerivedFunctorNatTrans,
      Iso.refl_inv, Iso.refl_hom]
    rw [Functor.rightDerivedNatTrans_app_assoc]
    simp only [NatTrans.id_app, Category.id_comp]
    rw [Functor.rightDerivedNatTrans_app_assoc]
    simp only [Functor.whiskerRight_app]
    rw [Functor.mapDerivedCategoryCompRightDerivedFunctorIso_hom_fac_app_assoc]
    have hi : (Functor.mapHomotopyCategoryCompIso
        (Iso.refl (x ⋙ G)) (.up ℤ)).inv.app P = 𝟙 _ := rfl
    simp only [Functor.mapDerivedCategoryCompRightDerivedFunctorUnit_app, hi]
    erw [DerivedCategory.Qh.map_id, Category.id_comp]
    simp only [Category.assoc]
    erw [← G.rightDerivedFunctor.map_comp, Iso.inv_hom_id_app,
      G.rightDerivedFunctor.map_id, Category.comp_id]
  simp only [Functor.mapHomotopyCategory_obj, HomotopyCategory.quotient_obj_as, P] at hnorm
  rw [factorsh_quotient, factorsh_quotient] at hnorm
  have hc : DerivedCategory.Qh.map
      ((NatTrans.mapHomotopyCategory c.hom (.up ℤ)).app P) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex c.hom (.up ℤ)).app I) := by
    exact DerivedCategory.Q.congr_map (by rfl)
  rw [hc] at hnorm
  simp only [Functor.rightDerivedFunctorUnitQ, DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Quotient.lift.isLift_hom, Quotient.lift.isLift_inv]
  erw [H.rightDerivedFunctor.map_id, G.rightDerivedFunctor.map_id]
  erw [Category.id_comp, Category.comp_id, Category.id_comp, Category.comp_id]
  exact hnorm

end SquareHelpers

section Limits

variable {A B : Type (u + 1)} [Category.{u} A] [Category.{u} B]
  [Abelian A] [Abelian B] [HasCountableProducts A] [HasCountableProducts B]
  [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B]
  (F : A ⥤ B) [F.Additive]

attribute [local implicit_reducible] roosTowerAction HomologicalComplex.asFunctor
  HomologicalComplex.complexOfFunctorsToFunctorToComplex
  Functor.mapHomologicalComplex NatTrans.mapHomologicalComplex
  HomologicalComplex.coneOfHasLimitEval strictTowerLimitIso

private abbrev towerF := (Functor.whiskeringRight ℕᵒᵖ A B).obj F
private abbrev complexF := F.mapHomologicalComplex (.up ℤ)
private abbrev limitComparison (K : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (complexF F).obj (limit K.asFunctor) ⟶ limit ((roosTowerAction F).obj K).asFunctor :=
  limit.post K.asFunctor (complexF F)

private theorem comparison_inclusion (K : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (complexF F).map (roosι K) ≫ roosAdditiveComparison F K =
      limitComparison F K ≫ roosι ((roosTowerAction F).obj K) := by
  have ha (n : ℕ) : limit.π K.asFunctor (op (n + 1)) ≫
      K.asFunctor.map (homOfLE (Nat.le_succ n)).op = limit.π K.asFunctor (op n) :=
    limit.w K.asFunctor _
  apply HomologicalComplex.Hom.ext
  funext k
  obtain ⟨p, rfl⟩ : ∃ p : ℤ, k = p + 1 := ⟨k - 1, by omega⟩
  apply (cancel_mono (roosχ ((roosTowerAction F).obj K) p).hom).mp
  have h := roosAdditiveComparison_augmentation F K (limit K.asFunctor)
    (fun n ↦ limit.π K.asFunctor (op n)) ha p
  change ((complexF F).map (roosι K) ≫ roosAdditiveComparison F K).f (p + 1) ≫ _ = _
    at h
  rw [h]
  simp only [HomologicalComplex.comp_f, Category.assoc, roosι_χ]
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.lift_fst]
    erw [biprod.lift_fst, comp_zero]
  · simp only [Category.assoc, biprod.lift_snd]
    have hl : limitComparison F K ≫
        Pi.lift (fun n : ℕ ↦ limit.π ((roosTowerAction F).obj K).asFunctor (op n)) =
      Pi.lift (fun n : ℕ ↦ (complexF F).map (limit.π K.asFunctor (op n))) := by
      apply Pi.hom_ext
      intro n
      rw [Category.assoc]
      erw [Pi.lift_π, Pi.lift_π]
      exact limit.post_π K.asFunctor (complexF F) (op n)
    exact congrArg (fun z ↦ z.f (p + 1)) hl.symm

omit [HasCountableProducts A] in
private theorem limitIso_projection
    (K : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕᵒᵖ) (p : ℤ) :
    ((strictTowerLimitIso).hom.app K).f p ≫ limit.π (K.X p) n =
      (limit.π K.asFunctor n).f p := by
  have h := congrArg (fun z ↦ z.f p)
    (limit.isoLimitCone_hom_π
      ⟨HomologicalComplex.coneOfHasLimitEval K.asFunctor,
        HomologicalComplex.isLimitConeOfHasLimitEval K.asFunctor⟩ n)
  dsimp only [HomologicalComplex.comp_f, HomologicalComplex.coneOfHasLimitEval] at h
  exact h

variable [PreservesLimitsOfShape ℕᵒᵖ F]

omit [HasCountableProducts A] [HasCountableProducts B] in
private theorem comparison_limitIso (K : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (complexF F).map ((strictTowerLimitIso).hom.app K) ≫
        (NatTrans.mapHomologicalComplex (preservesLimitNatIso (J := ℕᵒᵖ) F).hom
          (.up ℤ)).app K =
      limitComparison F K ≫ (strictTowerLimitIso).hom.app ((roosTowerAction F).obj K) := by
  apply HomologicalComplex.Hom.ext
  funext p
  apply limit.hom_ext
  intro n
  simp only [HomologicalComplex.comp_f, Category.assoc]
  change F.map (((strictTowerLimitIso).hom.app K).f p) ≫
      (preservesLimitIso F (K.X p)).hom ≫
        limit.π (K.X p ⋙ F) n = _
  rw [preservesLimitIso_hom_π, ← F.map_comp, limitIso_projection]
  erw [limitIso_projection]
  exact (congrArg (fun z ↦ z.f p)
    (limit.post_π K.asFunctor (complexF F) n)).symm

end Limits


section Coordinates

variable {A B : Type (u + 1)} [Category.{u} A] [Category.{u} B]
  [Abelian A] [Abelian B] [HasCountableProducts A] [HasCountableProducts B]
  (F : A ⥤ B) [F.Additive]

/-- The chosen invertible Roos comparison is the canonical additive map.
Source: Stacks Tag 0941, product-cone coordinates
(blueprint: lem-pur-roos-tensor-normalization).
Proof: cancel the target coordinate isomorphism in every degree, and use the
identical coordinate equations of the chosen and canonical maps. -/
private theorem chosenComparison_eq
    (hprod : ∀ L : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
      IsIso (piComparison (F.mapHomologicalComplex (.up ℤ))
        (fun n : ℕ ↦ L.asFunctor.obj (op n))))
    (L : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    ((strictRoosAdditiveComparison F hprod).choose L).hom = roosAdditiveComparison F L := by
  apply HomologicalComplex.Hom.ext
  funext k
  obtain ⟨p, rfl⟩ : ∃ p : ℤ, k = p + 1 := ⟨k - 1, by omega⟩
  apply (cancel_mono (strictRoosCoordinates ((roosTowerAction F).obj L) p).hom).mp
  exact ((strictRoosAdditiveComparison F hprod).choose_spec.1 L p).trans
    (roosAdditiveComparison_coordinates F L p).symm

/-- The canonical additive comparison preserves strict compatible augmentations.
Source: Stacks Tag 0941, ordinary-limit cone inclusion
(blueprint: lem-pur-roos-tensor-normalization).
Proof: applying the complex functor to each compatibility equation gives the
mapped compatible family. Both augmentation maps have coordinates (0,Fq),
by the established augmentation-coordinate formulas, so cancellation proves equality. -/
private theorem comparison_augmentation
    (K : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (P : CochainComplex A ℤ)
    (a : ∀ n : ℕ, P ⟶ K.asFunctor.obj (op n))
    (ha : ∀ n : ℕ, a (n + 1) ≫
      K.asFunctor.map (homOfLE (Nat.le_succ n)).op = a n) :
    ∃ h : ∀ n : ℕ,
      (F.mapHomologicalComplex (.up ℤ)).map (a (n + 1)) ≫
        ((roosTowerAction F).obj K).asFunctor.map
          (homOfLE (Nat.le_succ n)).op =
        (F.mapHomologicalComplex (.up ℤ)).map (a n),
      (F.mapHomologicalComplex (.up ℤ)).map (roosAugment a ha) ≫
          roosAdditiveComparison F K =
        roosAugment (fun n : ℕ ↦
          (F.mapHomologicalComplex (.up ℤ)).map (a n)) h := by
  have h (n : ℕ) : (F.mapHomologicalComplex (.up ℤ)).map (a (n + 1)) ≫
      ((roosTowerAction F).obj K).asFunctor.map
        (homOfLE (Nat.le_succ n)).op =
      (F.mapHomologicalComplex (.up ℤ)).map (a n) := by
    change (F.mapHomologicalComplex (.up ℤ)).map (a (n + 1)) ≫
      (F.mapHomologicalComplex (.up ℤ)).map
        (K.asFunctor.map (homOfLE (Nat.le_succ n)).op) = _
    rw [← Functor.map_comp, ha]
  refine ⟨h, ?_⟩
  apply HomologicalComplex.Hom.ext
  funext k
  obtain ⟨p, rfl⟩ : ∃ p : ℤ, k = p + 1 := ⟨k - 1, by omega⟩
  apply (cancel_mono (roosχ ((roosTowerAction F).obj K) p).hom).mp
  have hχ := roosAugment_χ
    (X := (roosTowerAction F).obj K) (P := (F.mapHomologicalComplex (.up ℤ)).obj P)
    (fun n : ℕ ↦ (F.mapHomologicalComplex (.up ℤ)).map (a n)) h p
  exact (roosAdditiveComparison_augmentation F K P a ha p).trans hχ.symm

end Coordinates

section Derived

variable {A B : Type (u + 1)} [Category.{u} A] [Category.{u} B]
  [Abelian A] [Abelian B] [HasCountableProducts A] [HasCountableProducts B]
  [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B]
  [HasDerivedCategory.{d} A] [HasDerivedCategory.{d} B]
  [HasDerivedCategory.{d} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{d} (ℕᵒᵖ ⥤ B)]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ B)]
  [(lim : (ℕᵒᵖ ⥤ A) ⥤ A).Additive] [(lim : (ℕᵒᵖ ⥤ B) ⥤ B).Additive]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesLimitsOfShape ℕᵒᵖ F]
  [PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ A B).obj F)]
  [PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ A B).obj F)]
  [((Functor.whiskeringRight ℕᵒᵖ A B).obj F).PreservesKInjectiveComplexes]

/-- The canonical derived tensor/limit comparison is the localization of the
coordinate tensor map, for any exact additive functor preserving tower limits
and tower K-injectives.
Source: Stacks Tag 0941; the product-cone comparison and its ordinary-limit unit
(blueprint: lem-pur-roos-tensor-normalization).
Proof: the coordinate comparison carries the ordinary Roos inclusion to the
limit comparison followed by the target inclusion. Degreewise limit projections
identify that comparison with the cochain map of the ordinary limit isomorphism.
The three defining factors of the canonical derived comparison obey the full
unit equation. On a K-injective tower the unit-normalized Roos inclusion is
invertible, so cancellation gives the claimed equation. Naturality along a
K-injective resolution gives the equation on every complex. -/
theorem roosTensorNormalization
    (κA : roosF (A := A) ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙
      (lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctor)
    (κB : roosF (A := B) ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙
      (lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctor)
    (hA : ∀ K, DerivedCategory.Q.map (roosι K) ≫ κA.hom.app K =
      DerivedCategory.Q.map
        (limit.isoLimitCone ⟨HomologicalComplex.coneOfHasLimitEval K.asFunctor,
          HomologicalComplex.isLimitConeOfHasLimitEval K.asFunctor⟩).hom ≫
        (lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctorUnitQ K)
    (hB : ∀ K, DerivedCategory.Q.map (roosι K) ≫ κB.hom.app K =
      DerivedCategory.Q.map
        (limit.isoLimitCone ⟨HomologicalComplex.coneOfHasLimitEval K.asFunctor,
          HomologicalComplex.isLimitConeOfHasLimitEval K.asFunctor⟩).hom ≫
        (lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctorUnitQ K)
    (K : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    let T := (Functor.whiskeringRight ℕᵒᵖ A B).obj F
    let τ := (Functor.rightDerivedFunctorCompMapDerivedCategoryIso
      (lim : (ℕᵒᵖ ⥤ A) ⥤ A) F).symm ≪≫
      Functor.rightDerivedFunctorNatIso (preservesLimitNatIso (J := ℕᵒᵖ) F) ≪≫
      Functor.mapDerivedCategoryCompRightDerivedFunctorIso T
        (lim : (ℕᵒᵖ ⥤ B) ⥤ B)
    F.mapDerivedCategory.map (κA.hom.app K) ≫ τ.hom.app (DerivedCategory.Q.obj K) =
      F.mapDerivedCategoryFactors.hom.app (roosF.obj K) ≫
        DerivedCategory.Q.map (roosAdditiveComparison F K) ≫
        κB.hom.app ((roosTowerAction F).obj K) ≫
        (lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctor.map
          (T.mapDerivedCategoryFactors.inv.app K) := by
  let HA : (ℕᵒᵖ ⥤ A) ⥤ A := lim
  let HB : (ℕᵒᵖ ⥤ B) ⥤ B := lim
  let T := towerF F
  let TC := roosTowerAction F
  let FD := F.mapDerivedCategory
  let τ := (Functor.rightDerivedFunctorCompMapDerivedCategoryIso HA F).symm ≪≫
    Functor.rightDerivedFunctorNatIso (preservesLimitNatIso (J := ℕᵒᵖ) F) ≪≫
    Functor.mapDerivedCategoryCompRightDerivedFunctorIso T HB
  let θ : roosF ⋙ complexF F ⟶ TC ⋙ roosF :=
    { app := roosAdditiveComparison F
      naturality := fun _ _ f ↦ roosAdditiveComparison_natural F f }
  let S := DerivedCategory.Q ⋙ T.mapDerivedCategory ⋙ HB.rightDerivedFunctor
  let δ : roosF ⋙ DerivedCategory.Q ⋙ FD ⟶ S :=
    Functor.whiskerRight κA.hom FD ≫ Functor.whiskerLeft DerivedCategory.Q τ.hom
  let δ' : roosF ⋙ DerivedCategory.Q ⋙ FD ⟶ S :=
    Functor.whiskerLeft roosF F.mapDerivedCategoryFactors.hom ≫
      Functor.whiskerRight θ DerivedCategory.Q ≫
      Functor.whiskerLeft TC κB.hom ≫
      Functor.whiskerRight T.mapDerivedCategoryFactors.inv HB.rightDerivedFunctor
  have hn := tensorSquare_normalized HA HB T F (preservesLimitNatIso (J := ℕᵒᵖ) F)
  have hδ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective] :
      δ.app I = δ'.app I := by
    have hu : IsIso (HA.rightDerivedFunctorUnitQ I) := by
      rw [Functor.rightDerivedFunctorUnitQ_eq]
      infer_instance
    have hlim : IsIso (DerivedCategory.Q.map ((strictTowerLimitIso).hom.app I)) :=
      inferInstanceAs (IsIso (DerivedCategory.Q.mapIso ((strictTowerLimitIso).app I)).hom)
    have hi : IsIso (DerivedCategory.Q.map (roosι I) ≫ κA.hom.app I) := by
      rw [hA]
      infer_instance
    have : IsIso (DerivedCategory.Q.map (roosι I)) :=
      IsIso.of_isIso_comp_right _ (κA.hom.app I)
    apply (cancel_epi (FD.map (DerivedCategory.Q.map (roosι I)))).mp
    dsimp only [δ, δ', NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app]
    rw [← FD.map_comp_assoc, hA, FD.map_comp, Category.assoc]
    have hh := hn I
    apply (cancel_mono (HB.rightDerivedFunctor.map (T.mapDerivedCategoryFactors.hom.app I))).mp
    simp only [Category.assoc, ← HB.rightDerivedFunctor.map_comp,
      Iso.inv_hom_id_app, HB.rightDerivedFunctor.map_id]
    erw [Category.comp_id, hh]
    have hf := F.mapDerivedCategoryFactors.hom.naturality (roosι I)
    change FD.map (DerivedCategory.Q.map (roosι I)) ≫
        F.mapDerivedCategoryFactors.hom.app (roosF.obj I) =
      F.mapDerivedCategoryFactors.hom.app (limit I.asFunctor) ≫
        DerivedCategory.Q.map ((complexF F).map (roosι I)) at hf
    erw [reassoc_of% hf, ← DerivedCategory.Q.map_comp_assoc, comparison_inclusion,
      DerivedCategory.Q.map_comp, Category.assoc, hB]
    have hf' := F.mapDerivedCategoryFactors.hom.naturality
      ((strictTowerLimitIso).hom.app I)
    change FD.map (DerivedCategory.Q.map ((strictTowerLimitIso).hom.app I)) ≫
        F.mapDerivedCategoryFactors.hom.app ((HA.mapHomologicalComplex (.up ℤ)).obj I) =
      F.mapDerivedCategoryFactors.hom.app (limit I.asFunctor) ≫
        DerivedCategory.Q.map ((complexF F).map ((strictTowerLimitIso).hom.app I)) at hf'
    erw [reassoc_of% hf', ← DerivedCategory.Q.map_comp_assoc, comparison_limitIso,
      DerivedCategory.Q.map_comp]
    simp only [Category.assoc]
    rfl
  obtain ⟨I, hI, j, _, hj⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective K
  have := hI
  have := hj
  have : IsIso (S.map j) := by
    change IsIso (HB.rightDerivedFunctor.map (T.mapDerivedCategory.map (DerivedCategory.Q.map j)))
    infer_instance
  have h : δ.app K = δ'.app K := by
    apply (cancel_mono (S.map j)).mp
    rw [← δ.naturality j, ← δ'.naturality j, hδ I]
  exact h

end Derived
end CategoryTheory.RoosTensor
