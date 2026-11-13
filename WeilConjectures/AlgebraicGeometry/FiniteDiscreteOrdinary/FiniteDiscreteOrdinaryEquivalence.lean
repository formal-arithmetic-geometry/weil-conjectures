/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteEncodingTensorTor
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteEncodingConstructibility
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingCompactification
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Finite discrete coefficient comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

omit [TopologicalSpace A] [IsTopologicalRing A] in
private theorem ordinaryLocalModel_of_iso (T : Scheme.{u})
    {M N : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A))}
    (e : M ≅ N) (h : ordinaryLocalModel A T M) : ordinaryLocalModel A T N := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C, fun i ↦ ?_⟩
  obtain ⟨P, hP, ⟨h⟩⟩ := hC i
  exact ⟨P, hP, ⟨(upperStar _ (C.f i)).mapIso e.symm ≪≫ h⟩⟩

omit [TopologicalSpace A] [IsTopologicalRing A] in
private theorem ordinaryStratified_of_iso (T : Scheme.{u})
    {M N : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A))}
    (e : M ≅ N) (h : ordinaryStratified A T M) : ordinaryStratified A T N := by
  obtain ⟨S, hS⟩ := h
  exact ⟨S, fun a ↦ ordinaryLocalModel_of_iso A _
    ((upperStar _ (S.immersion a)).mapIso e) (hS a)⟩

omit [TopologicalSpace A] [IsTopologicalRing A] in
private theorem ordinaryConstructible_of_iso (T : Scheme.{u})
    {M N : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A))}
    (e : M ≅ N) (h : ordinaryConstructible A T M) : ordinaryConstructible A T N := by
  classical
  unfold ordinaryConstructible at h ⊢
  split_ifs at h ⊢ with hT
  · exact ordinaryStratified_of_iso A T e h
  · intro U hU
    exact ordinaryStratified_of_iso A U.toScheme ((upperStar _ U.ι).mapIso e) (h U hU)

omit [TopologicalSpace A] [IsTopologicalRing A] in
private local instance ordinaryCtf_iso (T : Scheme.{u}) :
    (ordinaryCtf A T).IsClosedUnderIsomorphisms where
  of_iso e h := by
    refine ⟨⟨DerivedCategory.TStructure.t.bounded.prop_of_iso e h.1.1, ?_⟩,
      (DerivedCategory.finiteTorAmplitude _).prop_of_iso e h.2⟩
    intro n
    exact ordinaryConstructible_of_iso A T ((DerivedCategory.homologyFunctor _ n).mapIso e)
      (h.1.2 n)

section Localizing
universe w v₁ v₂
variable {C D : Type w} [Category.{v₁} C] [Category.{v₂} D]
  [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

private theorem inverseImageLocalizing (P : ObjectProperty D) (F : C ⥤ D)
    [F.CommShift ℤ] [F.IsTriangulated]
    [∀ I : Type w, PreservesColimitsOfShape (Discrete I) F]
    (hP : IsLocalizingSubcategory P) :
    IsLocalizingSubcategory (P.inverseImage F) := by
  let := hP.1
  let := hP.2.1
  refine ⟨inferInstance, inferInstance, ?_⟩
  intro I G hG hPG
  let := hG
  let : HasColimit (G ⋙ F) := ⟨_, isColimitOfPreserves F (colimit.isColimit G)⟩
  exact P.prop_of_iso (preservesColimitIso F G).symm
    (hP.2.2 (G ⋙ F) inferInstance hPG)

private theorem localizing_forward (S : ObjectProperty C) (T : ObjectProperty D)
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    [∀ I : Type w, PreservesColimitsOfShape (Discrete I) F]
    (hST : ∀ K, S K → T (F.obj K)) {K : C} (hK : localizingClosure S K) :
    localizingClosure T (F.obj K) := by
  intro P hP hT
  exact hK (P.inverseImage F) (inverseImageLocalizing P F hP)
    (fun L hL ↦ hT _ (hST L hL))

private theorem localizing_equivalence (S : ObjectProperty C) (T : ObjectProperty D)
    [T.IsClosedUnderIsomorphisms] (e : C ≌ D)
    [e.functor.CommShift ℤ] [e.functor.IsTriangulated]
    [e.inverse.CommShift ℤ] [e.inverse.IsTriangulated]
    (hST : ∀ K, S K ↔ T (e.functor.obj K)) (K : C) :
    localizingClosure S K ↔ localizingClosure T (e.functor.obj K) := by
  constructor
  · exact localizing_forward S T e.functor (fun L ↦ (hST L).1)
  · intro hK P hP hS
    let := hP.2.1
    have hi (L : D) (hL : T L) : S (e.inverse.obj L) :=
      (hST _).2 (T.prop_of_iso (e.counitIso.app L).symm hL)
    have h := localizing_forward T S e.inverse hi hK
    exact P.prop_of_iso (e.unitIso.app K).symm (h P hP hS)
end Localizing

/-- Finite discrete condensed and ordinary coefficients agree, including the exact
section-action equivalence, its actual unbounded termwise extension, relative derived
tensor, every ordered Tor interval, finite local models, bounded constructible finite-Tor
objects, triangulated and coproduct structure, localizing closures, and the two composites
for each fixed compactification. -/
theorem moduleObject_ordinary_coefficient_equivalence [Finite A] [DiscreteTopology A] :
    ∃ E : ∀ T : Scheme.{u}, Encoding A T,
      (∀ T : Scheme.{u},
        Nonempty ((E T).fixedDerived.functor.Monoidal) ∧
        (∀ (K : DerivedCategory (Internal A T)) (a b : ℤ), a ≤ b →
          (DerivedCategory.torAmplitudeIn _ a b K ↔
            Scheme.HasProEtaleTorAmplitude T A ((E T).ordinaryDerived.functor.obj K) a b)) ∧
        (∀ (K : DerivedCategory (Internal A T)) (a b : ℤ), a ≤ b →
          (DerivedCategory.torAmplitudeIn _ a b K ↔ DerivedCategory.torAmplitudeIn _ a b
            ((E T).fixedDerived.functor.obj K))) ∧
        (∀ M : Internal A T,
          HasFiniteConstantLocalModel (coefficient A) T M ↔
            ordinaryLocalModel A T (((E T).ordinary.functor ⋙ (E T).fixed.functor).obj M)) ∧
        (∀ K : DerivedCategory (Internal A T),
          (constantModelBoundedConstructible (coefficient A) T K ∧
            DerivedCategory.finiteTorAmplitude _ K) ↔
              ordinaryCtf A T ((E T).fixedDerived.functor.obj K)) ∧
        Nonempty ((E T).fixedDerived.functor.CommShift ℤ) ∧
        (E T).fixedDerived.functor.IsTriangulated ∧
        PreservesColimitsOfSize.{u + 1, u + 1} (E T).fixedDerived.functor ∧
        (∀ K : DerivedCategory (Internal A T),
          localizingClosureProEtale (coefficient A) T K ↔
            CategoryTheory.localizingClosure (ordinaryCtf A T)
              ((E T).fixedDerived.functor.obj K))) ∧
      (∀ (X Y : Scheme.{u}) (f : X ⟶ Y) (c : Compactification f),
        Nonempty (CondensedRing.rightDerivedLowerShriekOfCompactification (coefficient A) c ⋙
            (E Y).fixedDerived.functor ≅
          (E X).fixedDerived.functor ⋙
            rightDerivedLowerShriekOfCompactification
              (ModuleCat.{u + 1} (ULift.{u + 1} A)) c)) := by
  classical
  let E : ∀ T : Scheme.{u}, Encoding A T := fun T ↦ Classical.choice (encoding_exists A T)
  refine ⟨E, ?_, encoding_compactification A E⟩
  intro T
  obtain ⟨hm, ho, ht⟩ := encoding_tensor_tor A T (E T)
  obtain ⟨hl, hb⟩ := encoding_constructibility A T (E T)
  have hf (K : DerivedCategory (Internal A T)) :
      DerivedCategory.finiteTorAmplitude _ K ↔
        DerivedCategory.finiteTorAmplitude _ ((E T).fixedDerived.functor.obj K) := by
    constructor
    · rintro ⟨a, b, h⟩
      exact ⟨min a b, b, (ht K _ _ (min_le_right a b)).1
        (h.mono (min_le_left a b) le_rfl)⟩
    · rintro ⟨a, b, h⟩
      exact ⟨min a b, b, (ht K _ _ (min_le_right a b)).2
        (h.mono (min_le_left a b) le_rfl)⟩
  have hctf (K : DerivedCategory (Internal A T)) :
      (constantModelBoundedConstructible (coefficient A) T K ∧
        DerivedCategory.finiteTorAmplitude _ K) ↔
          ordinaryCtf A T ((E T).fixedDerived.functor.obj K) :=
    and_congr (hb K) (hf K)
  let : ((E T).ordinary.trans (E T).fixed).functor.Additive :=
    inferInstanceAs ((E T).ordinary.functor ⋙ (E T).fixed.functor).Additive
  let : ((E T).ordinary.trans (E T).fixed).inverse.Additive :=
    inferInstanceAs ((E T).fixed.inverse ⋙ (E T).ordinary.inverse).Additive
  let : (E T).fixedDerived.functor.IsTriangulated := by
    change ((E T).ordinary.functor ⋙ (E T).fixed.functor).mapDerivedCategory.IsTriangulated
    infer_instance
  let : (E T).fixedDerived.inverse.CommShift ℤ := by
    change ((E T).fixed.inverse ⋙ (E T).ordinary.inverse).mapDerivedCategory.CommShift ℤ
    infer_instance
  let : (E T).fixedDerived.inverse.IsTriangulated := by
    change ((E T).fixed.inverse ⋙ (E T).ordinary.inverse).mapDerivedCategory.IsTriangulated
    infer_instance
  exact ⟨hm, ho, ht, hl, hctf, ⟨inferInstance⟩, inferInstance, inferInstance,
    localizing_equivalence _ _ (E T).fixedDerived hctf⟩

end AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary
