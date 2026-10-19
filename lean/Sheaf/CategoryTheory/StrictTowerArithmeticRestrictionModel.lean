/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.StrictTowerArithmeticRestrictionDefs
import Sheaf.CategoryTheory.StrictTowerArithmeticRestrictionResolution
import Sheaf.CategoryTheory.StrictTowerArithmeticRestrictionCochainModel
import Sheaf.Algebra.Homology.KInjectiveProductsTermwise
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective

/-! # Localization of the arithmetic cochain comparison

Source: Stacks Project, Tags 0941 and 0H9K.
-/

@[expose] public section
set_option autoImplicit false
universe a b w uC vC r
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.StrictTowerArithmetic

private lemma productCone
    {A : Type a} [Category.{b} A] [Abelian A] [HasDerivedCategory.{w} A]
    [HasCountableProducts A] (T : ℕ → CochainComplex A ℤ)
    [∀ n : ℕ, (T n).IsKInjective] :
    Nonempty (IsLimit (DerivedCategory.Q.mapCone (limit.cone (Discrete.functor T)))) := by
  obtain ⟨_, h⟩ := CochainComplex.termwise_product_isKInjective_and_isLimit T
  have : PreservesLimit (Discrete.functor T) DerivedCategory.Q :=
    preservesLimit_of_preserves_limit_cone
      (HomologicalComplex.isLimitConeOfHasLimitEval (Discrete.functor T)) h.some
  exact ⟨isLimitOfPreserves DerivedCategory.Q (limit.isLimit _)⟩

/-- The cochain comparison, after localization, agrees with the normalized derived unit.
Source: Stacks Project, Tags 0941 and 0H9K
(blueprint: lem-sp-strict-tower-arithmetic-restriction-model).
Evaluate K-injectives and use their termwise product universal properties. Apply the
explicit cochain comparison, identify derived limits by the invertible units η and
the localized kernel comparisons, and cancel η in its normalization equation.
The first cone coordinate gives the projection identity; the strict kernel square gives
the cone-unit identity. -/
theorem strictTowerArithmeticRestrictionModel
    {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max uC vC r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC r}]
    (R : Sheaf J RingCat.{max uC vC r})
    (_hcomm : ∀ (U : Cᵒᵖ) (a b : R.obj.obj U), a * b = b * a)
    [HasDerivedCategory.{w} (ringedSiteModules.{max uC vC r} R)]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R)]
    (RF : DerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ⥤
      DerivedCategory.{w} (ringedSiteModules.{max uC vC r} R))
    (η : limitComplex (ringedSiteModules.{max uC vC r} R) ⋙ DerivedCategory.Q.{w} ⟶
      DerivedCategory.Q.{w} ⋙ RF)
    (_hRF : RF.IsRightDerivedFunctor η
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R)
        (ComplexShape.up ℤ)))
    (_hη : ∀ I, CochainComplex.IsKInjective I → IsIso (η.app I))
    (ρ : ∀ (e : ℕ), 1 ≤ e →
      (RF ≅ derivedRestriction (ringedSiteModules.{max uC vC r} R) e ⋙ RF))
    (hρ : ∀ (e : ℕ) (he : 1 ≤ e) X,
      η.app X ≫ (ρ e he).hom.app (DerivedCategory.Q.obj X) ≫
          RF.map ((restriction _ e).mapDerivedCategoryFactors.hom.app X) =
        DerivedCategory.Q.map (limitMap e X) ≫
          η.app ((complexRestriction _ e).obj X)) :
      (∀ (e : ℕ) (he : 1 ≤ e)
          (I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ),
        I.IsKInjective → (∀ i : ℤ, Injective (I.X i)) →
        (∀ n : ℕ, CochainComplex.IsKInjective (I.asFunctor.obj (op n))) ∧
        CochainComplex.IsKInjective ((complexRestriction _ e).obj I) ∧
        Nonempty (IsLimit (DerivedCategory.Q.mapCone
          (limit.cone (Discrete.functor (fun n : ℕ ↦ I.asFunctor.obj (op n)))))) ∧
        Nonempty (IsLimit (DerivedCategory.Q.mapCone
          (limit.cone (Discrete.functor
            (fun n : ℕ ↦ I.asFunctor.obj ((index e).obj (op n))))))) ∧
        boundary I ≫ block e I.asFunctor =
          selection e I.asFunctor ≫ boundary ((complexRestriction _ e).obj I) ∧
        ∃ (κ : (limitComplex _).obj I ⟶ model I)
          (κe : (limitComplex _).obj ((complexRestriction _ e).obj I) ⟶
            model ((complexRestriction _ e).obj I))
          (c : model I ⟶ model ((complexRestriction _ e).obj I))
          (σ : RF.obj (DerivedCategory.Q.obj I) ≅ DerivedCategory.Q.obj (model I))
          (σe : RF.obj (DerivedCategory.Q.obj ((complexRestriction _ e).obj I)) ≅
            DerivedCategory.Q.obj (model ((complexRestriction _ e).obj I))),
          QuasiIso κ ∧ QuasiIso κe ∧ QuasiIso c ∧
          (∀ (i : ℤ) (n : ℕ),
            κ.f i ≫ (CochainComplex.mappingCocone.fst (boundary I)).f i ≫
                (Pi.π (fun n : ℕ ↦ I.asFunctor.obj (op n)) n).f i =
              limit.π (I.X i) (op n)) ∧
          (∀ (i j : ℤ) (h : i + -1 = j),
            κ.f i ≫ (CochainComplex.mappingCocone.snd (boundary I)).v i j h = 0) ∧
          (∀ (i : ℤ) (n : ℕ),
            κe.f i ≫ (CochainComplex.mappingCocone.fst
                (boundary ((complexRestriction _ e).obj I))).f i ≫
                (Pi.π (fun n : ℕ ↦ I.asFunctor.obj ((index e).obj (op n))) n).f i =
              limit.π (((complexRestriction _ e).obj I).X i) (op n)) ∧
          (∀ (i j : ℤ) (h : i + -1 = j),
            κe.f i ≫ (CochainComplex.mappingCocone.snd
              (boundary ((complexRestriction _ e).obj I))).v i j h = 0) ∧
          c ≫ CochainComplex.mappingCocone.fst (boundary ((complexRestriction _ e).obj I)) =
            CochainComplex.mappingCocone.fst (boundary I) ≫ selection e I.asFunctor ∧
          (∀ (i j : ℤ) (h : i + -1 = j),
            c.f i ≫ (CochainComplex.mappingCocone.snd
                (boundary ((complexRestriction _ e).obj I))).v i j h =
              (CochainComplex.mappingCocone.snd (boundary I)).v i j h ≫
                (block e I.asFunctor).f j) ∧
          κ ≫ c = limitMap e I ≫ κe ∧
          η.app I ≫ σ.hom = DerivedCategory.Q.map κ ∧
          η.app ((complexRestriction _ e).obj I) ≫ σe.hom = DerivedCategory.Q.map κe ∧
          (ρ e he).hom.app (DerivedCategory.Q.obj I) ≫
              RF.map ((restriction _ e).mapDerivedCategoryFactors.hom.app I) ≫ σe.hom =
            σ.hom ≫ DerivedCategory.Q.map c ∧
          (∀ n : ℕ,
            (ρ e he).hom.app (DerivedCategory.Q.obj I) ≫
                RF.map ((restriction _ e).mapDerivedCategoryFactors.hom.app I) ≫ σe.hom ≫
                DerivedCategory.Q.map
                  (CochainComplex.mappingCocone.fst
                    (boundary ((complexRestriction _ e).obj I)) ≫
                    Pi.π (fun n : ℕ ↦ I.asFunctor.obj ((index e).obj (op n))) n) =
              σ.hom ≫ DerivedCategory.Q.map
                (CochainComplex.mappingCocone.fst (boundary I) ≫
                  Pi.π (fun n : ℕ ↦ I.asFunctor.obj (op n)) (e * (n + 1) - 1))) ∧
          (∀ (K : CochainComplex (ringedSiteModules.{max uC vC r} R) ℤ)
              (a : K ⟶ (limitComplex _).obj I),
            DerivedCategory.Q.map (a ≫ κ) ≫ DerivedCategory.Q.map c =
              DerivedCategory.Q.map (a ≫ limitMap e I ≫ κe))) := by
  intro e he I hKI hinj
  have := hKI
  let A := ringedSiteModules.{max uC vC r} R
  have hKr := restriction_preservesKInjectives A e he I
  have hk (n : ℕ) : CochainComplex.IsKInjective (I.asFunctor.obj (op n)) :=
    tower_evaluation_isKInjective A I (op n)
  have hke (n : ℕ) :
      CochainComplex.IsKInjective (I.asFunctor.obj ((index e).obj (op n))) :=
    tower_evaluation_isKInjective A I ((index e).obj (op n))
  obtain ⟨hsquare, κ, κe, c, hκ, hκe, hc, hκfst, hκsnd, hκefst, hκesnd,
    hcfst, hcsnd, hcomm⟩ := strictTowerArithmeticRestrictionCochainModel A e he I hinj
  have := _hη I hKI
  have := _hη _ hKr
  have := hκ
  have := hκe
  let σ := (asIso (η.app I)).symm ≪≫ asIso (DerivedCategory.Q.map κ)
  let σe := (asIso (η.app ((complexRestriction A e).obj I))).symm ≪≫
    asIso (DerivedCategory.Q.map κe)
  have hσ : η.app I ≫ σ.hom = DerivedCategory.Q.map κ := by simp [σ]
  have hσe : η.app ((complexRestriction A e).obj I) ≫ σe.hom =
      DerivedCategory.Q.map κe := by simp [σe]
  have hderived : (ρ e he).hom.app (DerivedCategory.Q.obj I) ≫
      RF.map ((restriction A e).mapDerivedCategoryFactors.hom.app I) ≫ σe.hom =
      σ.hom ≫ DerivedCategory.Q.map c := by
    apply (cancel_epi (η.app I)).1
    calc
      _ = DerivedCategory.Q.map (limitMap e I) ≫ DerivedCategory.Q.map κe := by
        have h := congrArg (fun f ↦ f ≫ σe.hom) (hρ e he I)
        simp only [Category.assoc] at h
        erw [hσe] at h
        exact h
      _ = DerivedCategory.Q.map κ ≫ DerivedCategory.Q.map c := by
        rw [← DerivedCategory.Q.map_comp, ← hcomm, DerivedCategory.Q.map_comp]
      _ = _ := by rw [← hσ, Category.assoc]
  refine ⟨hk, hKr, productCone _, productCone _, hsquare,
    κ, κe, c, σ, σe, hκ, hκe, hc, hκfst, hκsnd, hκefst, hκesnd,
    hcfst, hcsnd, hcomm, hσ, hσe, hderived, ?_, ?_⟩
  · intro n
    have hcoord : c ≫ CochainComplex.mappingCocone.fst
        (boundary ((complexRestriction A e).obj I)) ≫
          Pi.π (fun n : ℕ ↦ I.asFunctor.obj ((index e).obj (op n))) n =
        CochainComplex.mappingCocone.fst (boundary I) ≫
          Pi.π (fun n : ℕ ↦ I.asFunctor.obj (op n)) (e * (n + 1) - 1) := by
      rw [← Category.assoc, hcfst, Category.assoc]
      simp [selection]
    simpa only [Category.assoc, ← DerivedCategory.Q.map_comp, hcoord] using
      congrArg (fun f ↦ f ≫ DerivedCategory.Q.map
        (CochainComplex.mappingCocone.fst (boundary ((complexRestriction A e).obj I)) ≫
          Pi.π (fun n : ℕ ↦ I.asFunctor.obj ((index e).obj (op n))) n)) hderived
  · intro K a
    rw [← DerivedCategory.Q.map_comp, Category.assoc, hcomm]

end CategoryTheory.StrictTowerArithmetic
