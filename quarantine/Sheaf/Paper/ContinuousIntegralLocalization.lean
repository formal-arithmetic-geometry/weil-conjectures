/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import Sheaf.Paper.ContinuousConstructibleIntegralImage
public import Mathlib.CategoryTheory.Functor.OfSequence

/-! # The localization telescope of integral continuous coefficients -/

@[expose] public section

universe u v w x
open CategoryTheory Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

/-- The sequential diagram obtained by repeatedly multiplying an object by ℓ.
Source: Bhatt--Scholze, Lemma 6.8.2, localization telescope.
(blueprint: def-weil-pbc-integral-localization-telescope). -/
abbrev integralLocalizationSequence {C : Type v} [Category.{w} C] [Preadditive C] (K : C) :
    ℕ ⥤ C :=
  Functor.ofSequence (fun _ ↦ ℓ • 𝟙 K)

/-- Additive functors carry the scalar telescope to the same scalar telescope.
Source: functoriality of scalar multiplication in a preadditive category.
(blueprint: def-weil-pbc-integral-localization-telescope). -/
noncomputable def integralLocalizationSequenceMapIso
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    (F : A ⥤ B) [F.Additive] (K : A) :
    integralLocalizationSequence ℓ K ⋙ F ≅ integralLocalizationSequence ℓ (F.obj K) := by
  let α : integralLocalizationSequence ℓ K ⋙ F ⟶
      integralLocalizationSequence ℓ (F.obj K) :=
    NatTrans.ofSequence (fun _ ↦ 𝟙 _) (by
      intro n
      simp only [Functor.comp_map, integralLocalizationSequence,
        Functor.ofSequence_map_homOfLE_succ]
      change F.map (ℓ • 𝟙 K) ≫ 𝟙 (F.obj K) = 𝟙 (F.obj K) ≫ (ℓ • 𝟙 (F.obj K))
      rw [F.map_nsmul, F.map_id]
      simp)
  have : ∀ n, IsIso (α.app n) := fun n ↦ by
    change IsIso (𝟙 _)
    infer_instance
  have : IsIso α := NatIso.isIso_of_isIso_app α
  exact asIso α

/-- The localization-unit cocone for an additive adjunction whose localized object
has invertible multiplication by ℓ.
Source: Bhatt--Scholze, Lemma 6.8.2, localization telescope.
(blueprint: def-weil-pbc-integral-localization-telescope). -/
noncomputable def scalarLocalizationUnitCocone
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    {L : A ⥤ B} {U : B ⥤ A} [U.Additive] (adj : L ⊣ U) (K : A)
    [IsIso (ℓ • 𝟙 (L.obj K))] : Cocone (integralLocalizationSequence ℓ K) := by
  let t : End (L.obj K) := inv (ℓ • 𝟙 (L.obj K))
  refine ⟨U.obj (L.obj K), NatTrans.ofSequence
    (fun n ↦ adj.unit.app K ≫ U.map (t ^ n)) ?_⟩
  intro n
  simp only [integralLocalizationSequence, Functor.ofSequence_map_homOfLE_succ,
    Functor.const_obj_map]
  change (ℓ • 𝟙 K) ≫ (adj.unit.app K ≫ U.map (t ^ (n + 1))) =
    (adj.unit.app K ≫ U.map (t ^ n)) ≫ 𝟙 _
  rw [Category.comp_id]
  have hw : (ℓ • 𝟙 K) ≫ adj.unit.app K =
      adj.unit.app K ≫ U.map (ℓ • 𝟙 (L.obj K)) := by
    rw [U.map_nsmul, U.map_id]
    simp
  have ht : (ℓ • 𝟙 (L.obj K)) ≫ t ^ (n + 1) = t ^ n := by
    rw [pow_succ, End.mul_def, ← Category.assoc]
    simp only [t, IsIso.hom_inv_id, Category.id_comp]
  rw [← Category.assoc, hw, Category.assoc, ← U.map_comp, ht]

/-- The unit of integral localization, with its nth leg divided by ℓⁿ.
Source: Bhatt--Scholze, Lemma 6.8.2, localization telescope.
(blueprint: def-weil-pbc-integral-localization-telescope). -/
noncomputable def integralLocalizationCocone (X : Scheme.{u})
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) X))) :
    Cocone (integralLocalizationSequence ℓ K) := by
  have h := derived_nsmul_isIso ℓ E X ((integralScalarExtension ℓ E X).obj K)
  change IsIso (ℓ • 𝟙
    ((Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X)).leftDerivedFunctor.obj K)) at h
  exact scalarLocalizationUnitCocone ℓ
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap (integralScalarMap ℓ E) X)) K

/-- The same telescope in the universe of the small pro-etale sites.
Source: Bhatt--Scholze, Lemma 6.8.2, localization telescope.
(blueprint: def-weil-pbc-integral-localization-telescope). -/
abbrev integralLocalizationLiftedSequence {C : Type v} [Category.{w} C] [Preadditive C]
    (K : C) : ULift.{x} ℕ ⥤ C :=
  (ULift.orderIso : ULift.{x} ℕ ≃o ℕ).equivalence.functor ⋙ integralLocalizationSequence ℓ K

/-- Reindex the unit telescope along the order equivalence with the lifted natural numbers.
Source: Bhatt--Scholze, Lemma 6.8.2, localization telescope.
(blueprint: def-weil-pbc-integral-localization-telescope). -/
noncomputable def integralLocalizationLiftedCocone (X : Scheme.{u})
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) X))) :
    Cocone ((ULift.orderIso : ULift.{x} ℕ ≃o ℕ).equivalence.functor ⋙
      integralLocalizationSequence ℓ K) :=
  (integralLocalizationCocone ℓ E X K).whisker
    (ULift.orderIso : ULift.{x} ℕ ≃o ℕ).equivalence.functor

end AlgebraicGeometry.ProEtale.CondensedRing
