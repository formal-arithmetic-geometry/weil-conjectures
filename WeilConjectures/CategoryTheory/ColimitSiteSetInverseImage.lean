/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ArrowsFunctor
public import WeilConjectures.CategoryTheory.FinitePrecoverage
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Comma.Over.Basic
import WeilConjectures.CategoryTheory.ColimitSiteSetSectionPresentation
import WeilConjectures.CategoryTheory.ColimitSiteSetEvaluationPresentation
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit

/-! # A step in the filtered colimit site construction.

Source: Stacks Project, Sites, Tags 09YL and 0A35.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

private theorem exists_unit_transition
    {C D E : Type u} [SmallCategory C] [SmallCategory D] [SmallCategory E]
    (f : C ⥤ D) (g : D ⥤ E) (h : C ⥤ E)
    (T : GrothendieckTopology C) (S : GrothendieckTopology D)
    (R : GrothendieckTopology E)
    [f.IsContinuous T S] [g.IsContinuous S R] [h.IsContinuous T R]
    (eh : f ⋙ g = h) (G : Sheaf T (Type u)) :
    ∃ α : (sheafPullback f (Type u) T S).obj G ⟶
      (g.sheafPushforwardContinuous (Type u) S R).obj
        ((sheafPullback h (Type u) T R).obj G),
      ∀ X : C,
        Arrow.mk (((sheafAdjunctionContinuous f (Type u) T S).unit.app G).hom.app
          (op X) ≫ α.hom.app (op (f.obj X))) =
        Arrow.mk (((sheafAdjunctionContinuous h (Type u) T R).unit.app G).hom.app
          (op X)) := by
  subst h
  let A := sheafAdjunctionContinuous f (Type u) T S
  let H := (sheafPullback (f ⋙ g) (Type u) T R).obj G
  let η := (sheafAdjunctionContinuous (f ⋙ g) (Type u) T R).unit.app G
  let β : G ⟶ (f.sheafPushforwardContinuous (Type u) T S).obj
      ((g.sheafPushforwardContinuous (Type u) S R).obj H) := η
  refine ⟨(A.homEquiv G _).symm β, ?_⟩
  intro X
  have he := (A.homEquiv G _).apply_symm_apply β
  rw [A.homEquiv_unit] at he
  exact congrArg (fun k ↦ Arrow.mk (k.hom.app (op X))) he

/-- The inverse images to the colimit site preserve finite limits, and their sections are the
filtered colimits of the stage inverse-image sections along the unit-transposed transition
maps. Stacks Project, Sites, Tag 0A35. -/
theorem colimit_site_set_inverse_image
    (J : Type u) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (P : ∀ j : J, Precoverage (F.obj j))
    [∀ j, (P j).HasIsos] [∀ j, (P j).IsStableUnderFiniteComposition]
    [∀ j, (P j).IsStableUnderFiniteBaseChange] [∀ j, (P j).HasPullbacks]
    (hfinite : ∀ (j : J) (X : F.obj j) (R : Presieve X), R ∈ P j X →
      Finite R.uncurry)
    (hcover : ∀ (j k : J) (a : j ⟶ k) (X : F.obj j) (R : Presieve X),
      R ∈ P j X → R.map (F.map a).toFunctor ∈ P k ((F.map a).toFunctor.obj X))
    (hpullback : ∀ (j k : J) (a : j ⟶ k) (X Y Z : F.obj j) (R : Presieve X),
      R ∈ P j X → ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
        PreservesLimit (cospan f g) (F.map a).toFunctor)
    [∀ (j k : J) (a : j ⟶ k),
      (F.map a).toFunctor.IsContinuous (P j).toGrothendieck (P k).toGrothendieck]
    [∀ (j k : J) (a : j ⟶ k), PreservesFiniteLimits
      (sheafPullback (F.map a).toFunctor (Type u)
        (P j).toGrothendieck (P k).toGrothendieck)]
    (V : Cocone F)
    (hobjects : IsColimit (Cat.objects.mapCocone V))
    (harrows : IsColimit (Cat.arrows.mapCocone V))
    (Q : Precoverage V.pt)
    [Q.HasIsos] [Q.IsStableUnderFiniteComposition]
    [Q.IsStableUnderFiniteBaseChange] [Q.HasPullbacks]
    (hQ : (∀ (Y : V.pt) (R : Presieve Y), R ∈ Q Y ↔
          ∃ (j : J) (X : F.obj j) (S : Presieve X) (h : (V.ι.app j).toFunctor.obj X = Y),
            S ∈ P j X ∧ h ▸ S.map (V.ι.app j).toFunctor = R))
    (hVpullback : (∀ (j : J) (X Y Z : F.obj j) (R : Presieve X), R ∈ P j X →
            ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
              PreservesLimit (cospan f g) (V.ι.app j).toFunctor))
    [∀ j : J, (V.ι.app j).toFunctor.IsContinuous
      (P j).toGrothendieck Q.toGrothendieck] :
            (∀ j : J, Nonempty (PreservesFiniteLimits
              (sheafPullback (V.ι.app j).toFunctor (Type u)
                (P j).toGrothendieck Q.toGrothendieck))) ∧
            (∀ (i : J) (G : Sheaf (P i).toGrothendieck (Type u)),
              ∃ α : ∀ t : Under i,
                (sheafPullback (F.map t.hom).toFunctor (Type u)
                  (P i).toGrothendieck (P t.right).toGrothendieck).obj G ⟶
                ((V.ι.app t.right).toFunctor.sheafPushforwardContinuous (Type u)
                  (P t.right).toGrothendieck Q.toGrothendieck).obj
                  ((sheafPullback (V.ι.app i).toFunctor (Type u)
                    (P i).toGrothendieck Q.toGrothendieck).obj G),
                (∀ (t : Under i) (X : F.obj i),
                  Arrow.mk (((sheafAdjunctionContinuous (F.map t.hom).toFunctor (Type u)
                    (P i).toGrothendieck (P t.right).toGrothendieck).unit.app G).hom.app
                      (op X) ≫ (α t).hom.app (op ((F.map t.hom).toFunctor.obj X))) =
                  Arrow.mk (((sheafAdjunctionContinuous (V.ι.app i).toFunctor (Type u)
                    (P i).toGrothendieck Q.toGrothendieck).unit.app G).hom.app (op X))) ∧
                ∀ U : F.obj i,
                  ∃ (D : Under i ⥤ (Type u))
                    (E : ∀ t : Under i, D.obj t ≅
                      ((sheafPullback (F.map t.hom).toFunctor (Type u)
                        (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj.obj
                          (op ((F.map t.hom).toFunctor.obj U)))
                    (K : Cocone D)
                    (e : K.pt ≅ ((sheafPullback (V.ι.app i).toFunctor (Type u)
                      (P i).toGrothendieck Q.toGrothendieck).obj G).obj.obj
                        (op ((V.ι.app i).toFunctor.obj U))),
                    Nonempty (IsColimit K) ∧
                    (∀ t : Under i, Arrow.mk (K.ι.app t ≫ e.hom) =
                      Arrow.mk ((E t).hom ≫
                        (α t).hom.app (op ((F.map t.hom).toFunctor.obj U)))) ∧
                    ∀ (t t' : Under i) (b : t ⟶ t'),
                      ∃ θ :
                        (sheafPullback (F.map t.hom).toFunctor (Type u)
                          (P i).toGrothendieck (P t.right).toGrothendieck).obj G ⟶
                        ((F.map b.right).toFunctor.sheafPushforwardContinuous (Type u)
                          (P t.right).toGrothendieck (P t'.right).toGrothendieck).obj
                          ((sheafPullback (F.map t'.hom).toFunctor (Type u)
                            (P i).toGrothendieck (P t'.right).toGrothendieck).obj G),
                        (∀ X : F.obj i,
                          Arrow.mk
                            (((sheafAdjunctionContinuous (F.map t.hom).toFunctor (Type u)
                              (P i).toGrothendieck (P t.right).toGrothendieck).unit.app
                                G).hom.app (op X) ≫
                              θ.hom.app (op ((F.map t.hom).toFunctor.obj X))) =
                          Arrow.mk
                            (((sheafAdjunctionContinuous (F.map t'.hom).toFunctor (Type u)
                              (P i).toGrothendieck (P t'.right).toGrothendieck).unit.app
                                G).hom.app (op X))) ∧
                        Arrow.mk ((E t).hom ≫
                          θ.hom.app (op ((F.map t.hom).toFunctor.obj U))) =
                        Arrow.mk (D.map b ≫ (E t').hom)) := by
  classical
  constructor
  · intro i
    have hEval (Y : V.pt) := colimit_site_set_evaluation_presentation J F P
      hfinite hcover hpullback V hobjects harrows Q hQ hVpullback i Y
    have hPres : PreservesFiniteLimits
        (sheafPullback (V.ι.app i).toFunctor (Type u)
          (P i).toGrothendieck Q.toGrothendieck ⋙
          sheafToPresheaf Q.toGrothendieck (Type u)) := by
      apply preservesFiniteLimits_of_evaluation
      intro Y
      obtain ⟨A, c, hf, L, hL, ⟨e⟩⟩ := hEval Y.unop
      let := c
      let := hf
      let := hL.some
      let := comp_preservesFiniteLimits L (colim : (A ⥤ Type u) ⥤ Type u)
      exact preservesFiniteLimits_of_natIso e.symm
    let := hPres
    exact ⟨⟨fun K _ _ ↦
      preservesLimitsOfShape_of_reflects_of_preserves
        (sheafPullback (V.ι.app i).toFunctor (Type u)
          (P i).toGrothendieck Q.toGrothendieck)
        (sheafToPresheaf Q.toGrothendieck (Type u))⟩⟩
  · intro i G
    have hα (t : Under i) := exists_unit_transition
      (F.map t.hom).toFunctor (V.ι.app t.right).toFunctor (V.ι.app i).toFunctor
      (P i).toGrothendieck (P t.right).toGrothendieck Q.toGrothendieck
      (congrArg Cat.Hom.toFunctor (V.w t.hom)) G
    choose α hα using hα
    refine ⟨α, hα, ?_⟩
    have hθ (t t' : Under i) (b : t ⟶ t') := exists_unit_transition
      (F.map t.hom).toFunctor (F.map b.right).toFunctor (F.map t'.hom).toFunctor
      (P i).toGrothendieck (P t.right).toGrothendieck (P t'.right).toGrothendieck
      (by rw [← Cat.Hom.comp_toFunctor, ← F.map_comp, Under.w b]) G
    choose θ hθ using hθ
    intro U
    obtain ⟨D, E, K, e, hK, hι, hm⟩ := colimit_site_set_section_presentation
      J F P hfinite hcover hpullback V hobjects harrows Q hQ hVpullback i G
      α hα θ hθ U
    refine ⟨D, E, K, e, hK, hι, ?_⟩
    intro t t' b
    exact ⟨θ t t' b, hθ t t' b, hm t t' b⟩


end CategoryTheory
